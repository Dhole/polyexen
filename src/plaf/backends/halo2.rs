use crate::{
    expr::{self, ColumnKind, ColumnQuery, Expr, PlonkVar as Var},
    plaf::{Plaf, Witness},
};
use halo2_proofs::{
    circuit::{Cell, Layouter, RegionIndex, SimpleFloorPlanner, Value},
    halo2curves::group::ff::{Field, PrimeField},
    plonk::{
        Advice, Any, Circuit, Column, ConstraintSystem, Error, Expression, FirstPhase, Fixed,
        Instance, SecondPhase, ThirdPhase, VirtualCells,
    },
    poly::Rotation,
};
// use halo2_proofs::plonk::{Challenge as Halo2Challenge};
use num_bigint::BigUint;
use std::{collections::HashMap, fmt::Debug};

/// Type that implements a halo2 circuit from a Plaf
#[derive(Debug)]
pub struct PlafH2Circuit {
    pub plaf: Plaf,
    pub wit: Witness,
}

impl PlafH2Circuit {
    pub fn instance<F: PrimeField<Repr = [u8; 32]>>(&self) -> Vec<Vec<F>> {
        let public_len = self.plaf.columns.public.len();
        let mut instance_vec = vec![Vec::new(); public_len];

        if public_len > 0 {
            for copy in &self.plaf.copys {
                let (left_col, right_col) = &copy.columns;

                let (witness_col, public_col, offsets) = match (left_col.kind, right_col.kind) {
                    (ColumnKind::Witness, ColumnKind::Public) => {
                        (left_col, right_col, copy.offsets.clone())
                    }
                    (ColumnKind::Public, ColumnKind::Witness) => (
                        right_col,
                        left_col,
                        copy.offsets.iter().map(|(l, r)| (*r, *l)).collect(),
                    ),
                    (ColumnKind::Public, _) | (_, ColumnKind::Public) => {
                        unimplemented!("constraints between public and fixed column not supported")
                    }
                    _ => continue,
                };

                for (witness_offset, public_offset) in offsets {
                    if instance_vec[public_col.index].len() <= public_offset {
                        instance_vec[public_col.index].resize(public_offset + 1, F::ZERO);
                    }
                    instance_vec[public_col.index][public_offset] = self.wit.witness
                        [witness_col.index][witness_offset]
                        .as_ref()
                        .unwrap()
                        .to_field();
                }
            }
        }
        instance_vec
    }
}

#[derive(Debug, Clone)]
pub struct H2Columns {
    advice: Vec<Column<Advice>>,
    fixed: Vec<Column<Fixed>>,
    instance: Vec<Column<Instance>>,
    // challenges: Vec<Halo2Challenge>,
}

#[derive(Debug, Clone)]
pub struct H2Config {
    columns: H2Columns,
}

struct H2Queries<F: Field>(HashMap<(ColumnKind, usize, i32), Expression<F>>);

impl<F: Field> H2Queries<F> {
    fn new() -> Self {
        Self(HashMap::new())
    }

    fn get(
        &mut self,
        meta: &mut VirtualCells<'_, F>,
        columns: &H2Columns,
        kind: ColumnKind,
        index: usize,
        rotation: i32,
    ) -> Expression<F> {
        let e = self
            .0
            .entry((kind, index, rotation))
            .or_insert_with(|| match kind {
                ColumnKind::Witness => meta.query_advice(columns.advice[index], Rotation(rotation)),
                ColumnKind::Public => {
                    meta.query_instance(columns.instance[index], Rotation(rotation))
                }
                ColumnKind::Fixed => meta.query_fixed(columns.fixed[index], Rotation(rotation)),
            });
        e.clone()
    }
}

trait ToField<F: Field> {
    fn to_field(&self) -> F;
}

impl<F: PrimeField<Repr = [u8; 32]>> ToField<F> for BigUint {
    fn to_field(&self) -> F {
        let mut repr: [u8; 32] = [0; 32];
        let f_le = self.to_bytes_le();
        repr[..f_le.len()].clone_from_slice(&f_le);
        F::from_repr_vartime(repr).expect("value in field")
    }
}

trait ToHalo2Expr<F: Field> {
    fn to_halo2_expr(
        &self,
        meta: &mut VirtualCells<'_, F>,
        columns: &H2Columns,
        queries: &mut H2Queries<F>,
    ) -> Expression<F>;
}

impl<F: PrimeField<Repr = [u8; 32]>> ToHalo2Expr<F> for Expr<Var> {
    fn to_halo2_expr(
        &self,
        meta: &mut VirtualCells<'_, F>,
        columns: &H2Columns,
        queries: &mut H2Queries<F>,
    ) -> Expression<F> {
        use Expression::*;
        match self {
            Expr::Const(f) => Constant(f.to_field()),
            Expr::Var(v) => match v {
                Var::Query(ColumnQuery {
                    column: expr::Column { kind, index },
                    rotation,
                }) => queries.get(meta, columns, *kind, *index, *rotation),
                Var::Challenge { index: _, phase: _ } => {
                    // FIXME: Figure out a way to use challenges
                    // meta.query_challenge(columns.challenges[*index])
                    Constant(F::from(0x100))
                }
            },
            Expr::Sum(es) => {
                let mut iter = es.iter();
                let first = iter.next().unwrap().to_halo2_expr(meta, columns, queries);
                iter.fold(first, |acc, e| {
                    acc + e.to_halo2_expr(meta, columns, queries)
                })
            }
            Expr::Mul(es) => {
                let mut iter = es.iter();
                let first = iter.next().unwrap().to_halo2_expr(meta, columns, queries);
                iter.fold(first, |acc, e| {
                    acc * e.to_halo2_expr(meta, columns, queries)
                })
            }
            Expr::Neg(e) => -e.to_halo2_expr(meta, columns, queries),
            Expr::Pow(e, n) => {
                if *n == 0 {
                    Constant(F::from(1))
                } else {
                    let e = e.to_halo2_expr(meta, columns, queries);
                    (1..*n).fold(e.clone(), |acc, _| acc * e.clone())
                }
            }
        }
    }
}

#[allow(dead_code)]
struct _Cell {
    region_index: RegionIndex,
    row_offset: usize,
    column: Column<Any>,
}

assert_eq_size!(_Cell, Cell);

fn new_cell(column: Column<Any>, offset: usize) -> Cell {
    let cell = _Cell {
        region_index: RegionIndex::from(0),
        row_offset: offset,
        column,
    };
    // NOTE: We use unsafe here to construct a Cell, which doesn't have a public constructor.  This
    // helps us set the copy constraints easily (without having to store all assigned cells
    // previously)
    unsafe { std::mem::transmute::<_Cell, Cell>(cell) }
}

impl<F: PrimeField<Repr = [u8; 32]>> Circuit<F> for PlafH2Circuit {
    type Config = H2Config;
    type FloorPlanner = SimpleFloorPlanner;
    type Params = Plaf;

    fn without_witnesses(&self) -> Self {
        Self {
            plaf: self.plaf.clone(),
            wit: Witness {
                num_rows: self.wit.num_rows,
                columns: Vec::new(),
                witness: Vec::new(),
            },
        }
    }

    fn params(&self) -> Self::Params {
        // TODO: Avoid cloning by storing Plaf in a RefCell
        self.plaf.clone()
    }

    fn configure_with_params(meta: &mut ConstraintSystem<F>, params: Self::Params) -> Self::Config {
        let plaf = &params;
        // Allocate columns
        let mut advice_columns = Vec::new();
        for column in &plaf.columns.witness {
            advice_columns.push(match column.phase {
                0 => meta.advice_column_in(FirstPhase),
                1 => meta.advice_column_in(SecondPhase),
                2 => meta.advice_column_in(ThirdPhase),
                _ => panic!("Advice column at phase {} not supported", column.phase),
            });
        }
        let mut fixed_columns = Vec::new();
        for _column in &plaf.columns.fixed {
            fixed_columns.push(meta.fixed_column());
        }
        let mut instance_columns = Vec::new();
        for _column in &plaf.columns.public {
            instance_columns.push(meta.instance_column());
        }

        let to_column_any = |col: &expr::Column| -> Column<Any> {
            match col.kind {
                ColumnKind::Witness => advice_columns[col.index].into(),
                ColumnKind::Public => instance_columns[col.index].into(),
                ColumnKind::Fixed => fixed_columns[col.index].into(),
            }
        };

        // Enable equality for copy constrains
        for copy in &plaf.copys {
            meta.enable_equality(to_column_any(&copy.columns.0));
            meta.enable_equality(to_column_any(&copy.columns.1));
        }

        // let mut challenges = Vec::new();
        // for challenge in &self.plaf.info.challenges {
        //     challenges.push(match challenge.phase {
        //         0 => meta.challenge_usable_after(FirstPhase),
        //         1 => meta.challenge_usable_after(SecondPhase),
        //         2 => meta.challenge_usable_after(ThirdPhase),
        //         p => panic!("Challenge phase {} not supported", p),
        //     });
        // }
        let columns = H2Columns {
            advice: advice_columns,
            fixed: fixed_columns,
            instance: instance_columns,
            // challenges,
        };

        // Name columns for lookups
        for (index, column) in columns.advice.iter().enumerate() {
            meta.annotate_lookup_any_column(*column, || plaf.columns.witness[index].name());
        }
        for (index, column) in columns.fixed.iter().enumerate() {
            meta.annotate_lookup_any_column(*column, || plaf.columns.fixed[index].name());
        }

        // Set polynomial constraints
        meta.create_gate("main", |meta| {
            let mut queries = H2Queries::new();
            let mut constraints: Vec<(&'static str, Expression<F>)> = Vec::new();
            for poly in &plaf.polys {
                constraints.push((
                    Box::leak(poly.name.clone().into_boxed_str()),
                    poly.exp.to_halo2_expr(meta, &columns, &mut queries),
                ));
            }
            constraints
        });

        // Set lookups
        for lookup in &plaf.lookups {
            meta.lookup_any(Box::leak(lookup.name.clone().into_boxed_str()), |meta| {
                let mut queries = H2Queries::new();
                let mut map = Vec::new();
                for (lhs, rhs) in lookup.exps.0.iter().zip(lookup.exps.1.iter()) {
                    map.push((
                        lhs.to_halo2_expr(meta, &columns, &mut queries),
                        rhs.to_halo2_expr(meta, &columns, &mut queries),
                    ));
                }
                map
            });
        }

        // Set shuffles
        for shuffle in &plaf.shuffles {
            meta.shuffle(Box::leak(shuffle.name.clone().into_boxed_str()), |meta| {
                let mut queries = H2Queries::new();
                let mut map = Vec::new();
                for (lhs, rhs) in shuffle.exps.0.iter().zip(shuffle.exps.1.iter()) {
                    map.push((
                        lhs.to_halo2_expr(meta, &columns, &mut queries),
                        rhs.to_halo2_expr(meta, &columns, &mut queries),
                    ));
                }
                map
            });
        }

        Self::Config { columns }
    }

    fn configure(_meta: &mut ConstraintSystem<F>) -> Self::Config {
        unreachable!();
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        layouter.assign_region(
            || "main",
            |mut region| {
                // Name columns
                for (index, column) in config.columns.advice.iter().enumerate() {
                    region.name_column(|| self.plaf.columns.witness[index].name(), *column);
                }
                for (index, column) in config.columns.fixed.iter().enumerate() {
                    region.name_column(|| self.plaf.columns.fixed[index].name(), *column);
                }
                for (index, column) in config.columns.instance.iter().enumerate() {
                    region.name_column(|| self.plaf.columns.public[index].name(), *column);
                }

                // Assign fixed columns
                for (index, column) in self.plaf.fixed.iter().enumerate() {
                    for (row, value) in column.iter().enumerate() {
                        if let Some(value) = value {
                            region.assign_fixed::<_, F, _, _>(
                                || "",
                                config.columns.fixed[index],
                                row,
                                || Value::known(value.to_field()),
                            )?;
                        }
                    }
                }
                let to_column_any = |col: &expr::Column| -> Column<Any> {
                    match col.kind {
                        ColumnKind::Witness => config.columns.advice[col.index].into(),
                        ColumnKind::Public => config.columns.instance[col.index].into(),
                        ColumnKind::Fixed => config.columns.fixed[col.index].into(),
                    }
                };
                // Set copy constraints
                for copy in &self.plaf.copys {
                    let (left_col, right_col) = &copy.columns;

                    if left_col.kind == ColumnKind::Public || right_col.kind == ColumnKind::Public {
                        continue;
                    }
                    let left_col = to_column_any(left_col);
                    let right_col = to_column_any(right_col);
                    for (left_offset, right_offset) in &copy.offsets {
                        region.constrain_equal(
                            new_cell(left_col, *left_offset),
                            new_cell(right_col, *right_offset),
                        )?;
                    }
                }
                // Assign advice columns
                for (index, column) in self.wit.witness.iter().enumerate() {
                    for (row, value) in column.iter().enumerate() {
                        if let Some(value) = value {
                            region.assign_advice::<_, F, _, _>(
                                || "",
                                config.columns.advice[index],
                                row,
                                || Value::known(value.to_field()),
                            )?;
                        }
                    }
                }
                Ok(())
            },
        )?;

        // Set public inputs
        for copy in &self.plaf.copys {
            let (left_col, right_col) = &copy.columns;

            let (witness_col, public_col, offsets) = match (left_col.kind, right_col.kind) {
                (ColumnKind::Witness, ColumnKind::Public) => {
                    (left_col, right_col, copy.offsets.clone())
                }
                (ColumnKind::Public, ColumnKind::Witness) => (
                    right_col,
                    left_col,
                    copy.offsets.iter().map(|(l, r)| (*r, *l)).collect(),
                ),
                (ColumnKind::Public, ColumnKind::Public) => {
                    panic!("Cannot copy from public to public")
                }
                _ => continue,
            };
            for (witness_offset, public_offset) in offsets {
                let cell = new_cell(
                    (*config.columns.advice.get(witness_col.index).unwrap()).into(),
                    witness_offset,
                );

                layouter.constrain_instance(
                    cell,
                    *config.columns.instance.get(public_col.index).unwrap(),
                    public_offset,
                )?;
            }
        }
        Ok(())
    }
}
