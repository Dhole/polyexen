use crate::expr::{self, get_field_p, ColumnKind, Expr, PlonkVar as Var};
use halo2_proofs::{
    circuit::Value,
    halo2curves::group::ff::{Field, PrimeField},
    plonk::{
        Advice, Any, Assigned, Assignment, Challenge as Halo2Challenge, Circuit, Column,
        ConstraintSystem, Error, Fixed, FloorPlanner, Instance, Selector,
    },
};
use num_bigint::BigUint;
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
    // Poison(usize),
}

#[derive(Debug)]
pub struct Witness {
    num_rows: usize,
    columns: Vec<ColumnWitness>,
    // The advice cells in the circuit, arranged as [column][row].
    witness: Vec<Vec<Option<BigUint>>>,
}

/// Adaptor struct to format the witness columns assignments as CSV
pub struct WitnessDisplayCSV<'a>(pub &'a Witness);

impl Display for WitnessDisplayCSV<'_> {
    /// Format witness assignment as CSV
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let this = self.0;
        write!(f, "offset")?;
        for col in this.columns.iter() {
            write!(f, ",")?;
            write!(f, "{}", col.name())?;
        }
        writeln!(f)?;
        for row_idx in 0..this.num_rows {
            write!(f, "{}", row_idx)?;
            for col_idx in 0..this.columns.len() {
                write!(f, ",")?;
                if let Some(ref v) = this.witness[col_idx][row_idx] {
                    write!(f, "{}", v)?;
                }
            }
            writeln!(f)?;
        }

        Ok(())
    }
}

#[derive(Debug)]
struct WitnessAssembly<F: Field> {
    k: u32,
    // The instance cells in the circuit, arranged as [column][row].
    instance: Vec<Vec<F>>,
    // The advice cells in the circuit, arranged as [column][row].
    advice: Vec<Vec<CellValue<F>>>,
    // A range of available rows for assignment and copies.
    usable_rows: Range<usize>,
    challenges: Vec<F>,
    // region: Option<(String, HashMap<Column<Any>, String>)>,
    // regions: HashMap<String, HashMap<Column<Any>, String>>,
}

impl<F: Field> Assignment<F> for WitnessAssembly<F> {
    fn enter_region<NR, N>(&mut self, _name: N)
    where
        NR: Into<String>,
        N: FnOnce() -> NR,
    {
        // self.region = Some((name().into(), HashMap::new()));
    }

    fn exit_region(&mut self) {
        // let (name, annotations) = self.region.take().unwrap();
        // self.regions.insert(name, annotations);
    }

    fn enable_selector<A, AR>(
        &mut self,
        _: A,
        _selector: &Selector,
        _row: usize,
    ) -> Result<(), Error>
    where
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        Ok(())
    }

    fn query_instance(&self, column: Column<Instance>, row: usize) -> Result<Value<F>, Error> {
        if !self.usable_rows.contains(&row) {
            panic!(
                "query_instance: row={} not in usable_rows={:?}",
                row, self.usable_rows
            );
            // return Err(Error::not_enough_rows_available(self.k));
        }

        self.instance
            .get(column.index())
            .and_then(|column| column.get(row))
            .map(|v| Value::known(*v))
            .ok_or(Error::BoundsFailure)
    }

    fn assign_advice<V, VR, A, AR>(
        &mut self,
        _: A,
        column: Column<Advice>,
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
            panic!(
                "assign_advice: row={} not in usable_rows={:?}",
                row, self.usable_rows
            );
            // return Err(Error::not_enough_rows_available(self.k));
        }

        *self
            .advice
            .get_mut(column.index())
            .and_then(|v| v.get_mut(row))
            .ok_or(Error::BoundsFailure)? =
            CellValue::Assigned(to().into_field().evaluate().assign()?);

        Ok(())
    }

    fn assign_fixed<V, VR, A, AR>(
        &mut self,
        _: A,
        _column: Column<Fixed>,
        _row: usize,
        _to: V,
    ) -> Result<(), Error>
    where
        V: FnOnce() -> Value<VR>,
        VR: Into<Assigned<F>>,
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        Ok(())
    }

    fn copy(
        &mut self,
        _left_column: Column<Any>,
        _left_row: usize,
        _right_column: Column<Any>,
        _right_row: usize,
    ) -> Result<(), Error> {
        Ok(())
    }

    fn fill_from_row(
        &mut self,
        _col: Column<Fixed>,
        _from_row: usize,
        _to: Value<Assigned<F>>,
    ) -> Result<(), Error> {
        Ok(())
    }

    fn get_challenge(&self, challenge: Halo2Challenge) -> Value<F> {
        Value::known(self.challenges[challenge.index()])
    }

    fn push_namespace<NR, N>(&mut self, _: N)
    where
        NR: Into<String>,
        N: FnOnce() -> NR,
    {
        // TODO: Do something with namespaces :)
    }

    fn pop_namespace(&mut self, _: Option<String>) {
        // TODO: Do something with namespaces :)
    }

    fn annotate_column<A, AR>(&mut self, annotation: A, column: Column<Any>)
    where
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
    }
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
    region: Option<(String, HashMap<Column<Any>, String>)>,
    regions: HashMap<String, HashMap<Column<Any>, String>>,
}

impl<F: Field> Assignment<F> for Assembly<F> {
    fn enter_region<NR, N>(&mut self, name: N)
    where
        NR: Into<String>,
        N: FnOnce() -> NR,
    {
        self.region = Some((name().into(), HashMap::new()));
    }

    fn exit_region(&mut self) {
        let (name, annotations) = self.region.take().expect("exit from a region");
        self.regions.insert(name, annotations);
    }

    fn enable_selector<A, AR>(&mut self, _: A, selector: &Selector, row: usize) -> Result<(), Error>
    where
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        if !self.usable_rows.contains(&row) {
            panic!(
                "enable_selector: row={} not in usable_rows={:?}",
                row, self.usable_rows
            );
            // return Err(Error::not_enough_rows_available(self.k));
        }

        self.selectors[selector.index()][row] = true;

        Ok(())
    }

    fn query_instance(&self, _: Column<Instance>, row: usize) -> Result<Value<F>, Error> {
        if !self.usable_rows.contains(&row) {
            panic!(
                "query_instance: row={} not in usable_rows={:?}",
                row, self.usable_rows
            );
            // return Err(Error::not_enough_rows_available(self.k));
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
            panic!(
                "assign_fixed: row={} not in usable_rows={:?}",
                row, self.usable_rows
            );
            // return Err(Error::not_enough_rows_available(self.k));
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
            panic!(
                "copy: rows={:?} not in usable_rows={:?}",
                (left_row, right_row),
                self.usable_rows
            );
            // return Err(Error::not_enough_rows_available(self.k));
        }

        // TODO: Sort columns
        let columns = self
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
            panic!(
                "fill_from_row: from_row={} not in usable_rows={:?}",
                from_row, self.usable_rows
            );
            // return Err(Error::not_enough_rows_available(self.k));
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

    fn annotate_column<A, AR>(&mut self, annotation: A, column: Column<Any>)
    where
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        let (_, ref mut annotations) = self.region.as_mut().expect("annotate in a region");
        annotations.insert(column, annotation().into());
    }
}

#[derive(Debug, Clone)]
pub struct ColumnWitness {
    pub name: String,
    pub aliases: Vec<String>,
    pub phase: usize,
}

impl ColumnWitness {
    fn new(name: String, phase: usize) -> Self {
        Self {
            name,
            aliases: Vec::new(),
            phase,
        }
    }
    fn name(&self) -> &String {
        self.aliases.get(0).unwrap_or(&self.name)
    }
}

#[derive(Debug, Clone)]
pub struct ColumnFixed {
    pub name: String,
    pub aliases: Vec<String>,
}

impl ColumnFixed {
    fn new(name: String) -> Self {
        Self {
            name,
            aliases: Vec::new(),
        }
    }
    fn name(&self) -> &String {
        self.aliases.get(0).unwrap_or(&self.name)
    }
}

#[derive(Debug, Clone)]
pub struct ColumnPublic {
    pub name: String,
    pub aliases: Vec<String>,
}

impl ColumnPublic {
    fn new(name: String) -> Self {
        Self {
            name,
            aliases: Vec::new(),
        }
    }
    fn name(&self) -> &String {
        self.aliases.get(0).unwrap_or(&self.name)
    }
}

#[derive(Debug)]
pub struct Challenge {
    pub name: String,
    pub alias: Option<String>,
    pub phase: usize,
}

impl Challenge {
    fn new(name: String, phase: usize) -> Self {
        Self {
            name,
            alias: None,
            phase,
        }
    }
    fn name(&self) -> &String {
        self.alias.as_ref().unwrap_or(&self.name)
    }
}

#[derive(Debug, Default)]
pub struct Columns {
    pub witness: Vec<ColumnWitness>,
    pub fixed: Vec<ColumnFixed>,
    pub public: Vec<ColumnPublic>,
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
    pub fixed: Vec<Vec<Option<BigUint>>>,
}

impl Plaf {
    pub fn fmt_column<W: Write>(&self, f: &mut W, c: &expr::Column) -> fmt::Result {
        use ColumnKind::*;
        write!(
            f,
            "{}",
            match c.kind {
                Witness => self.columns.witness[c.index].name(),
                Public => self.columns.public[c.index].name(),
                Fixed => self.columns.fixed[c.index].name(),
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
                write!(f, "{}", self.info.challenges[*index].name())
            }
        }
    }
    pub fn set_challange_alias(&mut self, index: usize, name: String) {
        self.info.challenges[index].alias = Some(name)
    }
}

/// Adaptor struct to format the fixed columns assignments as CSV
pub struct PlafDisplayFixedCSV<'a>(pub &'a Plaf);

impl Display for PlafDisplayFixedCSV<'_> {
    /// Format fixed columns assignments as CSV
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let this = self.0;
        write!(f, "offset")?;
        for col in this.columns.fixed.iter() {
            write!(f, ",")?;
            write!(f, "{}", col.name())?;
        }
        writeln!(f)?;
        for row_idx in 0..this.info.num_rows {
            write!(f, "{}", row_idx)?;
            for col_idx in 0..this.columns.fixed.len() {
                write!(f, ",")?;
                if let Some(ref v) = this.fixed[col_idx][row_idx] {
                    write!(f, "{}", v)?;
                }
            }
            writeln!(f)?;
        }
        Ok(())
    }
}

/// Adaptor struct to format the entire Plaf as toml except for the Fixed Column assignments
pub struct PlafDisplayBaseTOML<'a>(pub &'a Plaf);

impl Display for PlafDisplayBaseTOML<'_> {
    /// Format entire Plaf as toml except for Fixed Columns assignments
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let this = self.0;
        writeln!(f, "[info]")?;
        writeln!(f, "num_rows = {}", this.info.num_rows)?;
        writeln!(f)?;

        writeln!(f, "[info.challenges]")?;
        for ch in &this.info.challenges {
            write!(f, "{} = {{ phase = {}", ch.name, ch.phase)?;
            if let Some(alias) = &ch.alias {
                writeln!(f, ", alias = \"{}\" }}", alias)?;
            } else {
                writeln!(f, "}}")?;
            }
        }
        writeln!(f)?;

        writeln!(f, "[columns.public]")?;
        for c in &this.columns.public {
            writeln!(f, "{} = {{ aliases = {:?} }}", c.name, c.aliases)?;
        }
        writeln!(f)?;

        writeln!(f, "[columns.fixed]")?;
        for c in &this.columns.fixed {
            writeln!(f, "{} = {{ aliases = {:?} }}", c.name, c.aliases)?;
        }
        writeln!(f)?;

        writeln!(f, "[columns.witness]")?;
        for c in &this.columns.witness {
            writeln!(
                f,
                "{} = {{ phase = {}, aliases = {:?} }}",
                c.name, c.phase, c.aliases
            )?;
        }
        writeln!(f)?;

        for p in &this.polys {
            writeln!(f, "[constraints.polys.\"{}\"]", p.name)?;
            write!(f, "c = \"")?;
            p.exp
                .fmt_ascii(f, &mut |f: &mut fmt::Formatter<'_>, v: &Var| {
                    this.fmt_var(f, v)
                })?;
            writeln!(f, "\"")?;
        }
        writeln!(f)?;

        for l in &this.lookups {
            writeln!(f, "[constraints.lookups.\"{}\"]", l.name)?;
            writeln!(f, "l = [")?;
            for (lhs, rhs) in l.exps.0.iter().zip(l.exps.1.iter()) {
                write!(f, "  [\"")?;
                lhs.fmt_ascii(f, &mut |f: &mut fmt::Formatter<'_>, v: &Var| {
                    this.fmt_var(f, v)
                })?;
                writeln!(f, "\",")?;
                write!(f, "   \"")?;
                rhs.fmt_ascii(f, &mut |f: &mut fmt::Formatter<'_>, v: &Var| {
                    this.fmt_var(f, v)
                })?;
                writeln!(f, "\"],")?;
            }
            writeln!(f, "]")?;
        }
        writeln!(f)?;

        for c in &this.copys {
            writeln!(f, "[[constraints.copys]]")?;
            write!(f, "columns = [\"")?;
            this.fmt_column(f, &c.columns.0)?;
            write!(f, "\", \"")?;
            this.fmt_column(f, &c.columns.1)?;
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

pub fn get_witness<F: Field + PrimeField<Repr = [u8; 32]>, ConcreteCircuit: Circuit<F>>(
    k: u32,
    circuit: &ConcreteCircuit,
    plaf: &Plaf,
    challenges: Vec<F>,
    instance: Vec<Vec<F>>,
) -> Result<Witness, Error> {
    let n = 1 << k;

    let mut cs = ConstraintSystem::default();
    let config = ConcreteCircuit::configure(&mut cs);

    let instance = instance
        .into_iter()
        .map(|mut instance| {
            if instance.len() > n - (cs.blinding_factors() + 1) {
                return Err(Error::InstanceTooLarge);
            }

            instance.resize(n, F::zero());
            Ok(instance)
        })
        .collect::<Result<Vec<_>, _>>()?;

    let advice = vec![vec![CellValue::Unassigned; n]; cs.num_advice_columns()];

    let mut assembly: WitnessAssembly<F> = WitnessAssembly {
        k,
        instance,
        advice,
        usable_rows: 0..n as usize - (cs.blinding_factors() + 1),
        challenges,
        // region: None,
        // regions: HashMap::new(),
    };

    ConcreteCircuit::FloorPlanner::synthesize(
        &mut assembly,
        circuit,
        config,
        cs.constants().clone(),
    )?;

    let mut witness = Witness {
        num_rows: n,
        columns: plaf.columns.witness.clone(),
        witness: vec![vec![]; plaf.columns.witness.len()],
    };

    for i in 0..plaf.columns.witness.len() {
        let mut column = vec![None; n];
        for (j, cell) in assembly.advice[i].iter().enumerate() {
            if let CellValue::Assigned(v) = cell {
                column[j] = Some(BigUint::from_bytes_le(&v.to_repr()[..]));
            }
        }
        witness.witness[i] = column;
    }

    Ok(witness)
}

pub fn gen_plaf<F: Field + PrimeField<Repr = [u8; 32]>, ConcreteCircuit: Circuit<F>>(
    k: u32,
    circuit: &ConcreteCircuit,
) -> Result<Plaf, Error> {
    let n = 1 << k;

    let mut cs = ConstraintSystem::default();
    let config = ConcreteCircuit::configure(&mut cs);

    let degree = cs.degree();

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
        region: None,
        regions: HashMap::new(),
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
        plaf.info
            .challenges
            .push(Challenge::new(format!("ch{}_{}", i, phase), phase as usize));
    }

    for i in 0..cs.num_fixed_columns() {
        plaf.columns
            .fixed
            .push(ColumnFixed::new(format!("f{:02}", i)));
    }
    for i in 0..cs.num_instance_columns() {
        plaf.columns
            .public
            .push(ColumnPublic::new(format!("i{:02}", i)));
    }
    let column_phase = cs.advice_column_phase();
    for i in 0..cs.num_advice_columns() {
        plaf.columns.witness.push(ColumnWitness::new(
            format!("w{:02}", i),
            column_phase[i] as usize,
        ));
    }

    for (region_name, region) in assembly.regions {
        for (column, name) in region.iter() {
            let name = name.clone();
            match column.column_type() {
                Any::Advice(..) => plaf.columns.witness[column.index()].aliases.push(name),
                Any::Fixed => plaf.columns.fixed[column.index()].aliases.push(name),
                Any::Instance => plaf.columns.public[column.index()].aliases.push(name),
            }
        }
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
    for i in 0..cs.num_fixed_columns() {
        let mut fixed = vec![None; n];
        for (j, cell) in assembly.fixed[i].iter().enumerate() {
            if let CellValue::Assigned(v) = cell {
                fixed[j] = Some(BigUint::from_bytes_le(&v.to_repr()[..]));
            }
        }
        plaf.fixed.push(fixed);
    }
    Ok(plaf)
}
