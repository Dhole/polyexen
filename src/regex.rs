use std::collections::HashMap;

use num_bigint::BigUint;

use crate::expr::{Expr, Var};

#[derive(Debug, Clone)]
pub enum ExprRegex {
    Sum(Box<ExprRegex>),
    Neg(Box<ExprRegex>),

    ExprExtract(String),
    ConstExtract(String),

    ArrayExact(usize, Vec<ExprRegex>),
}

impl ExprRegex {
    pub fn match_extract<V: Var>(&self, expr: &Expr<V>) -> Option<RegexExtraction<V>> {
        use ExprRegex::*;
        match *self {
            Sum(subregex) => {
                if let Expr::Sum(subexpr) = expr {
                    subregex.match_extract_array(*subexpr)
                } else {
                    None
                }
            }
            Neg(subregex) => {
                if let Expr::Neg(subexpr) = expr {
                    subregex.match_extract(subexpr)
                } else {
                    None
                }
            }

            ExprExtract(extract_id) => Some(RegexExtraction::<V> {
                exprs: HashMap::<String, Expr<V>>::from([(extract_id, *expr)]),
                ..Default::default()
            }),

            ConstExtract(extract_id) => {
                if let Expr::Const(constant) = *expr {
                    Some(RegexExtraction::<V> {
                        consts: HashMap::<String, BigUint>::from([(extract_id, constant)]),
                        ..Default::default()
                    })
                } else {
                    None
                }
            }

            ArrayExact(_, _) => None,
        }
    }

    fn match_extract_array<V: Var>(&self, exprs: Vec<Expr<V>>) -> Option<RegexExtraction<V>> {
        match *self {
            ExprRegex::ArrayExact(len, subregex_vec) => {
                if exprs.len() != len {
                    return None;
                }
                if subregex_vec.len() != len {
                    panic!(
                        "PolyRegex::ArrayExact has length {} but there are {} subregex",
                        len,
                        subregex_vec.len()
                    );
                }

                let mut extraction = RegexExtraction::default();

                for (i, subregex) in subregex_vec.iter().enumerate() {
                    if let Some(result) = subregex.match_extract(&exprs[i]) {
                        extraction.extend(&result);
                    } else {
                        return None;
                    };
                }

                Some(extraction)
            }

            _ => None,
        }
    }
}

#[derive(Debug)]
pub struct RegexExtraction<V: Var> {
    pub consts: HashMap<String, BigUint>,
    pub exprs: HashMap<String, Expr<V>>,
}

impl<V: Var> Default for RegexExtraction<V> {
    fn default() -> Self {
        Self {
            consts: Default::default(),
            exprs: Default::default(),
        }
    }
}

impl<V: Var> RegexExtraction<V> {
    pub fn extend(&mut self, other: &RegexExtraction<V>) {
        self.consts.extend(other.consts);
        self.exprs.extend(other.exprs);
    }
}
