use crate::expr::{Ex, Expr};

use num_bigint::{BigInt, BigUint, Sign};
use num_traits::{cast::ToPrimitive, One, Zero};
use std::collections::{HashMap, HashSet};

#[derive(Debug, Clone)]
pub enum Bound {
    Range(BigUint, BigUint), // x in [start..end]
    Set(Vec<BigUint>),       // non contiguous set
}

impl Bound {
    // TODO: Replace set by Iter
    pub fn new<I: IntoIterator<Item = BigUint>>(iter: I) -> Self {
        let one = BigUint::from(1u64);
        let mut set: Vec<BigUint> = iter.into_iter().collect();
        set.sort();
        let mut inc = set[0].clone();
        for v in &set {
            if *v != inc {
                return Self::Set(set);
            }
            inc += &one;
        }
        Self::Range(set[0].clone(), set[set.len() - 1].clone())
    }
    pub fn new_bool() -> Self {
        Self::Range(BigUint::from(0u64), BigUint::from(1u64))
    }
    pub fn new_u8() -> Self {
        Self::Range(BigUint::from(0u64), BigUint::from(0xffu64))
    }
    pub fn new_u16() -> Self {
        Self::Range(BigUint::from(0u64), BigUint::from(0xff_ffu64))
    }

    pub fn range_u64(&self) -> Option<(u64, u64)> {
        if let Self::Range(start, end) = self {
            if let (Some(start), Some(end)) = (start.to_u64(), end.to_u64()) {
                Some((start, end))
            } else {
                None
            }
        } else {
            None
        }
    }
    pub fn is_bool(&self) -> bool {
        if let Some((0, 1)) = self.range_u64() {
            true
        } else {
            false
        }
    }
    pub fn is_u8(&self) -> bool {
        if let Some((0, 0xff)) = self.range_u64() {
            true
        } else {
            false
        }
    }
    pub fn is_u16(&self) -> bool {
        if let Some((0, 0xff_ff)) = self.range_u64() {
            true
        } else {
            false
        }
    }
}

#[derive(Debug)]
pub struct Attrs {
    pub bound: Bound,
}

#[derive(Debug)]
pub struct Analysis {
    pub vars_attrs: HashMap<String, Attrs>,
}

impl Analysis {
    pub fn new() -> Self {
        Self {
            vars_attrs: HashMap::new(),
        }
    }
}

fn to_biguint(c: BigInt, p: &BigUint) -> BigUint {
    let (sign, c) = c.into_parts();
    if sign == Sign::Minus {
        p - c
    } else {
        c
    }
}

pub fn find_bounds_poly(e: &Ex, p: &BigUint, analysis: &mut Analysis) {
    let (exhaustive, solutions) = find_solutions(e);
    let mut var: Option<String> = None;
    let mut sols = Vec::new();
    for (v, c) in solutions {
        if let Some(prev_v) = &var {
            if v != *prev_v {
                var = None;
                break;
            }
        } else {
            var = Some(v);
        }
        sols.push(c);
    }
    if let Some(var) = var {
        if let Some(attrs) = analysis.vars_attrs.get(&var) {
            unimplemented!();
        } else {
            analysis.vars_attrs.insert(
                var,
                Attrs {
                    bound: Bound::new(sols.into_iter().map(|c| to_biguint(c, p))),
                },
            );
        }
    }
}

// Attempt to find solutions to `e(X) == 0` by matching on the pattern `(x - A)(y - B)...`.
// Returns true when the solutions returned are exhaustive.
pub fn find_solutions(e: &Ex) -> (bool, Vec<(String, BigInt)>) {
    use Expr::*;
    fn find_solutions_base(e: &Ex) -> (bool, Vec<(String, BigInt)>) {
        match e {
            Const(_) => (true, Vec::new()),
            Var(v) => (true, vec![(v.clone(), BigInt::zero())]),
            Neg(e) => find_solutions_base(e),
            Sum(es) => {
                let mut var: Option<String> = None;
                let mut con: Option<BigInt> = None;
                let mut neg = false;
                for e in es {
                    match (e, &var, &con) {
                        (Const(c), _, None) => {
                            neg ^= true;
                            con = Some(c.clone().into());
                        }
                        (Var(v), None, _) => {
                            var = Some(v.clone());
                        }
                        (Neg(e), _, _) => match (&**e, &var, &con) {
                            (Const(c), _, None) => {
                                con = Some(c.clone().into());
                            }
                            (Var(v), None, _) => {
                                neg ^= true;
                                var = Some(v.clone());
                            }
                            _ => return (false, Vec::new()),
                        },
                        _ => return (false, Vec::new()),
                    }
                }
                if neg {
                    con = Some(-con.unwrap());
                }
                (true, vec![(var.unwrap(), con.unwrap())])
            }
            _ => (false, Vec::new()),
        }
    }
    match e {
        Mul(es) => {
            let mut exhaustive = true;
            let mut solutions = Vec::new();
            for e in es {
                let (e_exhaustive, e_solutions) = find_solutions_base(e);
                exhaustive &= e_exhaustive;
                solutions.extend_from_slice(&e_solutions);
            }
            (exhaustive, solutions)
        }
        _ => find_solutions_base(e),
    }
}

#[cfg(test)]
mod tests_with_parser {
    use super::*;
    use crate::parser::parse_expr;

    #[test]
    fn test_find_solutions() {
        for (e_str, sol_str, expected_exh) in [
            ("(a - 5) * (b + 8)", vec![("a", "5"), ("b", "-8")], true),
            ("(a - 5) * (a - 7)", vec![("a", "5"), ("a", "7")], true),
            ("(-a + 5) * (-a - 7)", vec![("a", "5"), ("a", "-7")], true),
            ("(a - 3) * -(a - 4)", vec![("a", "3"), ("a", "4")], true),
            ("(a - 3) * (a + b - 4)", vec![("a", "3")], false),
            (
                "(a - 0) * (a - 1) * (a - 2) * (a - 3)",
                vec![("a", "0"), ("a", "1"), ("a", "2"), ("a", "3")],
                false,
            ),
        ] {
            let e = parse_expr(e_str).unwrap();
            let mut expected_solutions = Vec::new();
            for s in sol_str {
                let v = s.0.to_string();
                let c = BigInt::parse_bytes(s.1.as_bytes(), 10).unwrap();
                expected_solutions.push((v, c));
            }
            expected_solutions.sort();

            let (exhaustive, mut solutions) = find_solutions(&e);
            solutions.sort();
            assert_eq!(exhaustive, expected_exh);
            assert_eq!(solutions, expected_solutions, "{}", e_str);
        }
    }

    #[test]
    fn test_find_bounds_poly() {
        let p = BigUint::parse_bytes(b"100000000000000000000000000000000", 16).unwrap()
            - BigUint::from(159u64);

        let poly1 = parse_expr("(a - 0) * (a - 1)").unwrap();
        let mut analysis = Analysis::new();
        find_bounds_poly(&poly1, &p, &mut analysis);
        assert_eq!(
            analysis.vars_attrs.get("a").unwrap().bound.range_u64(),
            Some((0, 1))
        );

        let poly2 = parse_expr("(a - 0) * (a - 1) * (a - 2) * (a - 3)").unwrap();
        let mut analysis = Analysis::new();
        find_bounds_poly(&poly2, &p, &mut analysis);
        assert_eq!(
            analysis.vars_attrs.get("a").unwrap().bound.range_u64(),
            Some((0, 3))
        );
    }
}
