use crate::expr::{self, get_field_p, ColumnKind, Expr, PlonkVar as Var};
use halo2_proofs::{
    circuit::Value,
    halo2curves::group::ff::{Field, PrimeField},
    plonk::{
        Advice, Any, Assigned, Assignment, Challenge as Halo2Challenge, Circuit, Column,
        ConstraintSystem, Error, Fixed, FloorPlanner, Instance, Selector,
    },
};
use std::collections::HashMap;
use std::fmt::{self, Debug, Display, Write};
use std::ops::Range;

/// The value of a particular cell within the circuit.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum CellValue<F> {
    // An unassigned cell.
    Unassigned,
    // A cell that has been assigned a value.
    Assigned(F),
    // A unique poisoned cell.
    Poison(usize),
}

/// Assembly to be used in circuit synthesis.
#[derive(Debug)]
struct Assembly<F: Field> {
    k: u32,
    fixed: Vec<Vec<CellValue<F>>>,
    // permutation: permutation::keygen::Assembly,
    copies: HashMap<(Column<Any>, Column<Any>), Vec<(usize, usize)>>,
    selectors: Vec<Vec<bool>>,
    // A range of available rows for assignment and copies.
    usable_rows: Range<usize>,
    _marker: std::marker::PhantomData<F>,
}

impl<F: Field> Assignment<F> for Assembly<F> {
    fn enter_region<NR, N>(&mut self, _: N)
    where
        NR: Into<String>,
        N: FnOnce() -> NR,
    {
        // Do nothing; we don't care about regions in this context.
    }

    fn exit_region(&mut self) {
        // Do nothing; we don't care about regions in this context.
    }

    fn enable_selector<A, AR>(&mut self, _: A, selector: &Selector, row: usize) -> Result<(), Error>
    where
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        if !self.usable_rows.contains(&row) {
            return Err(Error::not_enough_rows_available(self.k));
        }

        self.selectors[selector.index()][row] = true;

        Ok(())
    }

    fn query_instance(&self, _: Column<Instance>, row: usize) -> Result<Value<F>, Error> {
        if !self.usable_rows.contains(&row) {
            return Err(Error::not_enough_rows_available(self.k));
        }

        // There is no instance in this context.
        Ok(Value::unknown())
    }

    fn assign_advice<V, VR, A, AR>(
        &mut self,
        _: A,
        _: Column<Advice>,
        _: usize,
        _: V,
    ) -> Result<(), Error>
    where
        V: FnOnce() -> Value<VR>,
        VR: Into<Assigned<F>>,
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        // We only care about fixed columns here
        Ok(())
    }

    fn assign_fixed<V, VR, A, AR>(
        &mut self,
        _: A,
        column: Column<Fixed>,
        row: usize,
        to: V,
    ) -> Result<(), Error>
    where
        V: FnOnce() -> Value<VR>,
        VR: Into<Assigned<F>>,
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        if !self.usable_rows.contains(&row) {
            return Err(Error::not_enough_rows_available(self.k));
        }

        *self
            .fixed
            .get_mut(column.index())
            .and_then(|v| v.get_mut(row))
            .ok_or(Error::BoundsFailure)? =
            CellValue::Assigned(to().into_field().evaluate().assign()?);

        Ok(())
    }

    fn copy(
        &mut self,
        left_column: Column<Any>,
        left_row: usize,
        right_column: Column<Any>,
        right_row: usize,
    ) -> Result<(), Error> {
        if !self.usable_rows.contains(&left_row) || !self.usable_rows.contains(&right_row) {
            return Err(Error::not_enough_rows_available(self.k));
        }

        // TODO: Sort columns
        let mut columns = self
            .copies
            .entry((left_column.clone(), right_column.clone()))
            .or_insert_with(|| Vec::new());
        columns.push((left_row, right_row));
        Ok(())
    }

    fn fill_from_row(
        &mut self,
        column: Column<Fixed>,
        from_row: usize,
        to: Value<Assigned<F>>,
    ) -> Result<(), Error> {
        if !self.usable_rows.contains(&from_row) {
            return Err(Error::not_enough_rows_available(self.k));
        }

        for row in self.usable_rows.clone().skip(from_row) {
            self.assign_fixed(|| "", column, row, || to)?;
        }

        Ok(())
    }

    fn get_challenge(&self, _: Halo2Challenge) -> Value<F> {
        Value::unknown()
    }

    fn push_namespace<NR, N>(&mut self, _: N)
    where
        NR: Into<String>,
        N: FnOnce() -> NR,
    {
        // Do nothing; we don't care about namespaces in this context.
    }

    fn pop_namespace(&mut self, _: Option<String>) {
        // Do nothing; we don't care about namespaces in this context.
    }
}

#[derive(Debug)]
pub struct ColumnWitness {
    pub name: String,
    pub phase: usize,
}

#[derive(Debug)]
pub struct Challenge {
    pub name: String,
    pub phase: usize,
}

#[derive(Debug, Default)]
pub struct Columns {
    pub witness: Vec<ColumnWitness>,
    pub fixed: Vec<String>,
    pub public: Vec<String>,
}

#[derive(Debug)]
pub struct Poly {
    pub name: String,
    pub exp: Expr<Var>,
}

#[derive(Debug)]
pub struct Lookup {
    pub name: String,
    pub exps: (Vec<Expr<Var>>, Vec<Expr<Var>>),
}

#[derive(Debug)]
pub struct CopyC {
    pub columns: (expr::Column, expr::Column),
    pub offsets: Vec<(usize, usize)>,
}

#[derive(Debug, Default)]
pub struct Info {
    pub num_rows: usize,
    pub challenges: Vec<Challenge>,
}

// Plonkish Arithmetization Format
#[derive(Debug, Default)]
pub struct Plaf {
    pub info: Info,
    pub columns: Columns,
    pub polys: Vec<Poly>,
    pub lookups: Vec<Lookup>,
    pub copys: Vec<CopyC>,
}

impl Plaf {
    pub fn fmt_column<W: Write>(&self, f: &mut W, c: &expr::Column) -> fmt::Result {
        use ColumnKind::*;
        write!(
            f,
            "{}",
            match c.kind {
                Witness => &self.columns.witness[c.index].name,
                Public => &self.columns.public[c.index],
                Fixed => &self.columns.fixed[c.index],
            }
        )
    }
    pub fn fmt_var<W: Write>(&self, f: &mut W, v: &Var) -> fmt::Result {
        match v {
            Var::ColumnQuery { column, rotation } => {
                self.fmt_column(f, column)?;
                if *rotation != 0 {
                    write!(f, "[{}]", rotation)?;
                }
                Ok(())
            }
            Var::Challenge { index, phase: _ } => {
                write!(f, "{}", self.info.challenges[*index].name)
            }
        }
    }
}

impl Display for Plaf {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "[info]")?;
        writeln!(f, "num_rows = {}", self.info.num_rows)?;
        writeln!(f)?;

        writeln!(f, "[info.challenges]")?;
        for ch in &self.info.challenges {
            writeln!(f, "{} = {{ phase = {} }}", ch.name, ch.phase)?;
        }
        writeln!(f)?;

        writeln!(f, "[columns.public]")?;
        for c in &self.columns.public {
            writeln!(f, "{} = {{}}", c)?;
        }
        writeln!(f)?;

        writeln!(f, "[columns.fixed]")?;
        for c in &self.columns.fixed {
            writeln!(f, "{} = {{}}", c)?;
        }
        writeln!(f)?;

        writeln!(f, "[columns.witness]")?;
        for c in &self.columns.witness {
            writeln!(f, "{} = {{ phase = {} }}", c.name, c.phase)?;
        }
        writeln!(f)?;

        writeln!(f, "[constraints.polys]")?;
        for p in &self.polys {
            write!(f, "\"{}\" = \"", p.name)?;
            p.exp
                .fmt_ascii(f, &mut |f: &mut fmt::Formatter<'_>, v: &Var| {
                    self.fmt_var(f, v)
                })?;
            writeln!(f, "\"")?;
        }
        writeln!(f)?;

        writeln!(f, "[constraints.lookups]")?;
        for l in &self.lookups {
            write!(f, "\"{}\" = [[", l.name)?;
            for (i, lhs) in l.exps.0.iter().enumerate() {
                write!(f, "\"{}\"", lhs)?;
                if i != l.exps.0.len() - 1 {
                    write!(f, ", ")?;
                }
            }
            write!(f, "], [")?;
            for (i, rhs) in l.exps.1.iter().enumerate() {
                write!(f, "\"{}\"", rhs)?;
                if i != l.exps.1.len() - 1 {
                    write!(f, ", ")?;
                }
            }
            writeln!(f, "]")?;
        }
        writeln!(f)?;

        for c in &self.copys {
            writeln!(f, "[[constraints.copys]]")?;
            write!(f, "columns = [\"")?;
            self.fmt_column(f, &c.columns.0)?;
            write!(f, "\", \"")?;
            self.fmt_column(f, &c.columns.1)?;
            writeln!(f, "\"]")?;
            writeln!(f, "offsets = [")?;
            for (a, b) in &c.offsets {
                writeln!(f, " [{}, {}],", a, b)?;
            }
            writeln!(f, "]")?;
        }
        writeln!(f)?;

        Ok(())
    }
}

pub fn get_ir<F: Field + PrimeField<Repr = [u8; 32]>, ConcreteCircuit: Circuit<F>>(
    k: u32,
    circuit: &ConcreteCircuit,
) -> Result<(), Error> {
    let n = 1 << k;

    let mut cs = ConstraintSystem::default();
    let config = ConcreteCircuit::configure(&mut cs);

    let degree = cs.degree();
    println!("Degree = {}", degree);

    if n < cs.minimum_rows() {
        panic!("not enough rows available, k = {}", k);
    }

    let mut assembly: Assembly<F> = Assembly {
        k,
        fixed: vec![vec![CellValue::Unassigned; n]; cs.num_fixed_columns()],
        copies: HashMap::new(),
        selectors: vec![vec![false; n as usize]; cs.num_selectors()],
        usable_rows: 0..n as usize - (cs.blinding_factors() + 1),
        _marker: std::marker::PhantomData,
    };

    ConcreteCircuit::FloorPlanner::synthesize(
        &mut assembly,
        circuit,
        config,
        cs.constants().clone(),
    )?;

    let (cs, selector_polys) = cs.compress_selectors(assembly.selectors.clone());
    assembly
        .fixed
        .extend(selector_polys.into_iter().map(|poly| {
            let mut v = vec![CellValue::Unassigned; n];
            for (v, p) in v.iter_mut().zip(&poly[..]) {
                *v = CellValue::Assigned(*p);
            }
            v
        }));
    let mut plaf = Plaf::default();
    let p = get_field_p::<F>();

    plaf.info.num_rows = 2usize.pow(k);
    let challenge_phase = cs.challenge_phase();
    for i in 0..cs.num_challenges() {
        let phase = challenge_phase[i];
        plaf.info.challenges.push(Challenge {
            name: format!("ch{}_{}", i, phase),
            phase: phase as usize,
        });
    }

    for i in 0..cs.num_fixed_columns() {
        plaf.columns.fixed.push(format!("f{:02}", i));
    }
    for i in 0..cs.num_instance_columns() {
        plaf.columns.public.push(format!("i{:02}", i));
    }
    let column_phase = cs.advice_column_phase();
    for i in 0..cs.num_advice_columns() {
        plaf.columns.witness.push(ColumnWitness {
            name: format!("w{:02}", i),
            phase: column_phase[i] as usize,
        });
    }
    for gate in cs.gates() {
        let name = gate.name();
        let len_log10 = (gate.polynomials().len() as f64).log10().ceil() as usize;
        for (i, poly) in gate.polynomials().iter().enumerate() {
            let exp = Expr::<Var>::from(poly);
            let exp = exp.simplify(&p);
            if matches!(exp, Expr::Const(_)) {
                // Skip constant expressions (which should be `p(x) = 0`)
                continue;
            }
            plaf.polys.push(Poly {
                name: format!("{} {:0decimals$}", name, i, decimals = len_log10),
                exp,
            });
        }
    }
    for lookup in cs.lookups() {
        let name = lookup.name();
        let lhs = lookup.input_expressions();
        let rhs = lookup.table_expressions();
        let lhs = lhs
            .iter()
            .map(|e| Expr::<Var>::from(e).simplify(&p))
            .collect();
        let rhs = rhs
            .iter()
            .map(|e| Expr::<Var>::from(e).simplify(&p))
            .collect();
        plaf.lookups.push(Lookup {
            name: name.to_string(),
            exps: (lhs, rhs),
        })
    }
    let column_any_to_kind = |ct: &Any| match ct {
        Any::Advice(_) => ColumnKind::Witness,
        Any::Fixed => ColumnKind::Fixed,
        Any::Instance => ColumnKind::Public,
    };
    for ((col_a, col_b), offsets) in assembly.copies {
        plaf.copys.push(CopyC {
            columns: (
                expr::Column {
                    kind: column_any_to_kind(col_a.column_type()),
                    index: col_a.index(),
                },
                expr::Column {
                    kind: column_any_to_kind(col_b.column_type()),
                    index: col_b.index(),
                },
            ),
            offsets,
        });
    }
    println!("{}", plaf);
    Ok(())
}
