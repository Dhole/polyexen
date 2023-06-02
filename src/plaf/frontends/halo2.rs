use crate::{
    expr::{self, get_field_p, ColumnKind, ColumnQuery, Expr, PlonkVar as Var},
    plaf::{
        CellValue, Challenge, ColumnFixed, ColumnPublic, ColumnWitness, CopyC, Lookup, Plaf, Poly,
        Shuffle, Witness,
    },
};
use halo2_proofs::{
    circuit::Value,
    halo2curves::group::ff::{Field, PrimeField},
    plonk::{
        Advice, Any, Assigned, Assignment, Challenge as Halo2Challenge, Circuit, Column,
        ConstraintSystem, Error, Expression, Fixed, FixedQuery, FloorPlanner, Instance, Selector,
    },
    poly::Rotation,
};
use num_bigint::BigUint;
use num_traits::One;
use std::{collections::HashMap, fmt::Debug, ops::Range};

#[derive(Debug)]
struct WitnessAssembly<F: Field> {
    // k: u32,
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
        assert!(
            self.usable_rows.contains(&row),
            "row={}, usable_rows={:?}",
            row,
            self.usable_rows
        );

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
        assert!(
            self.usable_rows.contains(&row),
            "row={}, usable_rows={:?}",
            row,
            self.usable_rows
        );
        let cell = self
            .advice
            .get_mut(column.index())
            .and_then(|v| v.get_mut(row))
            .ok_or(Error::BoundsFailure)?;

        let mut known = false;
        to().into_field().evaluate().map(|f| {
            known = true;
            *cell = CellValue::Assigned(f);
        });
        if !known {
            return Err(Error::Synthesis);
        }

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

    fn annotate_column<A, AR>(&mut self, _annotation: A, _column: Column<Any>)
    where
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
    }
}

/// Assembly to be used in circuit synthesis.
#[derive(Debug)]
struct Assembly<F: Field> {
    // k: u32,
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
        assert!(
            self.usable_rows.contains(&row),
            "row={} not in usable_rows={:?}",
            row,
            self.usable_rows
        );

        self.selectors[selector.index()][row] = true;

        Ok(())
    }

    fn query_instance(&self, _: Column<Instance>, row: usize) -> Result<Value<F>, Error> {
        assert!(
            self.usable_rows.contains(&row),
            "row={}, usable_rows={:?}",
            row,
            self.usable_rows
        );

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
        assert!(
            self.usable_rows.contains(&row),
            "row={}, usable_rows={:?}",
            row,
            self.usable_rows
        );

        let cell = self
            .fixed
            .get_mut(column.index())
            .and_then(|v| v.get_mut(row))
            .ok_or(Error::BoundsFailure)?;

        let mut known = false;
        to().into_field().evaluate().map(|f| {
            known = true;
            *cell = CellValue::Assigned(f);
        });
        if !known {
            return Err(Error::Synthesis);
        }

        Ok(())
    }

    fn copy(
        &mut self,
        left_column: Column<Any>,
        left_row: usize,
        right_column: Column<Any>,
        right_row: usize,
    ) -> Result<(), Error> {
        assert!(
            self.usable_rows.contains(&left_row) && self.usable_rows.contains(&right_row),
            "left_row={}, right_row={}, usable_rows={:?}",
            left_row,
            right_row,
            self.usable_rows
        );

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
        assert!(
            self.usable_rows.contains(&from_row),
            "row={}, usable_rows={:?}",
            from_row,
            self.usable_rows
        );

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

pub fn gen_witness<F: Field + PrimeField<Repr = [u8; 32]>, ConcreteCircuit: Circuit<F>>(
    k: u32,
    circuit: &ConcreteCircuit,
    plaf: &Plaf,
    challenges: Vec<F>,
    instance: Vec<Vec<F>>,
) -> Result<Witness, Error> {
    let n = 1 << k;

    let mut cs = ConstraintSystem::default();
    let config = ConcreteCircuit::configure_with_params(&mut cs, circuit.params());

    let instance = instance
        .into_iter()
        .map(|mut instance| {
            if instance.len() > n - (cs.blinding_factors() + 1) {
                return Err(Error::InstanceTooLarge);
            }

            instance.resize(n, F::ZERO);
            Ok(instance)
        })
        .collect::<Result<Vec<_>, _>>()?;

    let advice = vec![vec![CellValue::Unassigned; n]; cs.num_advice_columns()];

    let mut assembly: WitnessAssembly<F> = WitnessAssembly {
        // k,
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

    let mut witness = plaf.gen_empty_witness();

    for i in 0..plaf.columns.witness.len() {
        let column = &mut witness.witness[i];
        for (j, cell) in assembly.advice[i].iter().enumerate() {
            if let CellValue::Assigned(v) = cell {
                column[j] = Some(BigUint::from_bytes_le(&v.to_repr()[..]));
            }
        }
    }

    Ok(witness)
}

pub fn expression_to_var<F: Field>(e: &Expression<F>) -> Option<Var> {
    use Var::*;
    match e {
        Expression::Fixed(q) => Some(Query(ColumnQuery {
            column: expr::Column {
                kind: ColumnKind::Fixed,
                index: q.column_index(),
            },
            rotation: q.rotation().0,
        })),
        Expression::Advice(q) => Some(Query(ColumnQuery {
            column: expr::Column {
                kind: ColumnKind::Witness,
                index: q.column_index(),
            },
            rotation: q.rotation().0,
        })),
        Expression::Instance(q) => Some(Query(ColumnQuery {
            column: expr::Column {
                kind: ColumnKind::Public,
                index: q.column_index(),
            },
            rotation: q.rotation().0,
        })),
        Expression::Challenge(c) => Some(Challenge {
            index: c.index(),
            phase: c.phase() as usize,
        }),
        _ => None,
    }
}

#[allow(dead_code)]
fn convert_query_names<F: Field>(
    map: &HashMap<Expression<F>, String>,
) -> HashMap<ColumnQuery, String> {
    let mut new_map = HashMap::new();
    use Var::*;
    for (e, name) in map.iter() {
        if let Some(v) = expression_to_var(e) {
            if let Query(q) = v {
                new_map.insert(q, name.clone());
            }
        }
    }
    new_map
}

#[derive(Copy, Clone, Debug)]
pub struct _FixedQuery {
    /// Query index
    pub index: Option<usize>,
    /// Column index
    pub column_index: usize,
    /// Rotation of this query
    pub rotation: Rotation,
}

assert_eq_size!(_FixedQuery, FixedQuery);

fn new_fixed_query(index: Option<usize>, column_index: usize, rotation: Rotation) -> FixedQuery {
    let fixed_query = _FixedQuery {
        index,
        column_index,
        rotation,
    };
    unsafe { std::mem::transmute::<_FixedQuery, FixedQuery>(fixed_query) }
}

fn replace_selectors_no_compress<F: Field>(expr: &mut Expression<F>, fixed_offset: usize) {
    *expr = expr.evaluate(
        &|constant| Expression::Constant(constant),
        &|selector| {
            Expression::Fixed(new_fixed_query(
                None,
                fixed_offset + selector.index(),
                Rotation(0),
            ))
        },
        &|query| Expression::Fixed(query),
        &|query| Expression::Advice(query),
        &|query| Expression::Instance(query),
        &|challenge| Expression::Challenge(challenge),
        &|a| -a,
        &|a, b| a + b,
        &|a, b| a * b,
        &|a, f| a * f,
    );
}

pub fn get_plaf<F: Field + PrimeField<Repr = [u8; 32]>, ConcreteCircuit: Circuit<F>>(
    k: u32,
    circuit: &ConcreteCircuit,
) -> Result<Plaf, Error> {
    let compress_selectors = true;
    let n = 1 << k;

    let mut cs = ConstraintSystem::default();
    let config = ConcreteCircuit::configure_with_params(&mut cs, circuit.params());

    // let degree = cs.degree();

    assert!(
        n >= cs.minimum_rows(),
        "n={}, minimum_rows={}",
        n,
        cs.minimum_rows()
    );

    let mut assembly: Assembly<F> = Assembly {
        // k,
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

    // Number of fixed columns before converting selectors into fixed columns
    let num_fixed_columns_orig = cs.num_fixed_columns();
    let cs = if compress_selectors {
        let (cs, selector_polys) = cs.compress_selectors(assembly.selectors.clone());
        // TODO: Turn selectors in query_names into new selector expressions from fixed columns
        assembly
            .fixed
            .extend(selector_polys.into_iter().map(|poly| {
                let mut v = vec![CellValue::Unassigned; n];
                for (v, p) in v.iter_mut().zip(&poly[..]) {
                    *v = CellValue::Assigned(*p);
                }
                v
            }));
        cs
    } else {
        cs
        // Substitute selectors for the real fixed columns in all gates
        // for expr in cs
        //     .gates_mut()
        //     .iter_mut()
        //     .flat_map(|gate| gate.polynomials_mut().iter_mut())
        // {
        //     replace_selectors_no_compress(expr, num_fixed_columns_orig);
        // }
        // Substitute non-simple selectors for the real fixed columns in all
        // lookup expressions
        //for expr in cs.lookups_mut().iter_mut().flat_map(|lookup| {
        //    lookup
        //        .input_expressions
        //        .iter_mut()
        //        .chain(lookup.table_expressions.iter_mut())
        //}) {
        //    replace_selectors_no_compress(expr, num_fixed_columns_orig);
        //}
        // Substitute selectors for the real fixed columns in all query_name expressions
        // TODO:
        // for (sel_expr, _map) in cs.query_names_mut().iter_mut() {
        //     replace_selectors_no_compress(sel_expr, num_fixed_columns_orig);
        // }
        // cs.num_fixed_columns += cs.num_selectors();

        // assembly.fixed.extend(assembly.selectors.iter().map(|col| {
        //     let mut v = vec![CellValue::Unassigned; n];
        //     for (v, p) in v.iter_mut().zip(&col[..]) {
        //         *v = CellValue::Assigned(if *p { F::ONE } else { F::ZERO });
        //     }
        //     v
        // }));
        // cs
    };

    let mut plaf = Plaf::default();
    let p = get_field_p::<F>();
    plaf.info.p = p;

    plaf.info.num_rows = 2usize.pow(k);
    let challenge_phase = cs.challenge_phase();
    for i in 0..cs.num_challenges() {
        let phase = challenge_phase[i];
        plaf.info
            .challenges
            .push(Challenge::new(format!("ch{}_{}", i, phase), phase as usize));
    }

    for i in 0..cs.num_fixed_columns() {
        let name = if i < num_fixed_columns_orig {
            format!("f{:02}", i)
        } else {
            // This should only happen when `compress_selectors = true`, otherwise
            // `num_fixed_columns_orig == cs.num_fixed_columns()`
            format!("s{:02}", i - num_fixed_columns_orig)
        };
        plaf.columns.fixed.push(ColumnFixed::new(name));
    }
    // If `compress_selectors = true`, then there should be 0 selectors in `cs`.
    for i in 0..cs.num_selectors() {
        let name = format!("s{:02}", i);
        plaf.columns.fixed.push(ColumnFixed::new(name));
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
    for (column, name) in cs.general_column_annotations().iter() {
        match column.column_type() {
            Any::Advice(_) => plaf.columns.witness[column.index()]
                .aliases
                .push(name.clone()),
            Any::Fixed => plaf.columns.fixed[column.index()]
                .aliases
                .push(name.clone()),
            Any::Instance => plaf.columns.public[column.index()]
                .aliases
                .push(name.clone()),
        }
    }

    for (_region_name, region) in assembly.regions {
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
            let exp = if !compress_selectors {
                // Substitute selectors for the real fixed columns in all gates
                let mut poly = poly.clone();
                replace_selectors_no_compress(&mut poly, num_fixed_columns_orig);
                Expr::<Var>::from(&poly)
            } else {
                Expr::<Var>::from(poly)
            };
            // let exp = exp.simplify(&p);
            if matches!(exp, Expr::Const(_)) {
                // Skip constant expressions (which should be `p(x) = 0`)
                continue;
            }
            plaf.polys.push(Poly {
                name: format!(
                    "{} {:0decimals$} -> {n}",
                    name,
                    i,
                    decimals = len_log10,
                    n = gate.constraint_name(i)
                ),
                // query_names: query_names.clone(),
                exp,
            });
        }
    }
    // TODO: Add support for query_names in halo2
    // plaf.metadata.query_names = cs
    //     .query_names()
    //     .iter()
    //     .map(|(selector, map)| (Expr::<Var>::from(selector), convert_query_names(map)))
    //     .collect();

    for lookup in cs.lookups() {
        let name = lookup.name();
        let lhs = lookup.input_expressions();
        let rhs = lookup.table_expressions();
        let (lhs, rhs) = if !compress_selectors {
            // Substitute non-simple selectors for the real fixed columns in all
            // lookup expressions
            let (mut lhs, mut rhs) = (lhs.clone(), rhs.clone());
            lhs.iter_mut()
                .chain(rhs.iter_mut())
                .for_each(|ref mut exp| replace_selectors_no_compress(exp, num_fixed_columns_orig));
            (
                lhs.iter().map(|e| Expr::<Var>::from(e)).collect(),
                rhs.iter().map(|e| Expr::<Var>::from(e)).collect(),
            )
        } else {
            (
                lhs.iter().map(|e| Expr::<Var>::from(e)).collect(),
                rhs.iter().map(|e| Expr::<Var>::from(e)).collect(),
            )
        };
        plaf.lookups.push(Lookup {
            name: name.to_string(),
            exps: (lhs, rhs),
        })
    }

    for shuffle in cs.shuffles() {
        let name = shuffle.name();
        let lhs = shuffle.input_expressions();
        let rhs = shuffle.shuffle_expressions();
        let (lhs, rhs) = if !compress_selectors {
            // Substitute non-simple selectors for the real fixed columns in all
            // shuffle expressions
            let (mut lhs, mut rhs) = (lhs.clone(), rhs.clone());
            lhs.iter_mut()
                .chain(rhs.iter_mut())
                .for_each(|ref mut exp| replace_selectors_no_compress(exp, num_fixed_columns_orig));
            (
                lhs.iter().map(|e| Expr::<Var>::from(e)).collect(),
                rhs.iter().map(|e| Expr::<Var>::from(e)).collect(),
            )
        } else {
            (
                lhs.iter().map(|e| Expr::<Var>::from(e)).collect(),
                rhs.iter().map(|e| Expr::<Var>::from(e)).collect(),
            )
        };
        plaf.shuffles.push(Shuffle {
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
    // If `compress_selectors = true`, then there should be 0 selectors in `cs`.
    for i in 0..cs.num_selectors() {
        let mut fixed = vec![None; n];
        for (j, enabled) in assembly.selectors[i].iter().enumerate() {
            if *enabled {
                fixed[j] = Some(BigUint::one());
            }
        }
        plaf.fixed.push(fixed);
    }

    Ok(plaf)
}
