use crate::expr::{modinv, mul, neg, Expr, Var};
use std::fmt::{self, Display};

use num_bigint::{BigInt, BigUint, Sign};
use num_traits::{cast::ToPrimitive, One, Zero};
use std::collections::{hash_map::RandomState, HashMap, HashSet};

#[derive(Debug, Clone, PartialEq)]
pub enum Bound {
    Range(BigUint, BigUint), // x in [start..end]
    Set(Vec<BigUint>),       // non contiguous set, always sorted
}

impl Display for Bound {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Bound::Range(start, end) => write!(f, "[{}:{}]", start, end),
            // Bound::Set(xs) => write!(f, "{:?}", xs),
            Bound::Set(xs) => {
                let mut s = format!("{:?}", xs);
                s.truncate(10);
                write!(f, "{}", s)
            }
        }
    }
}

impl Bound {
    pub fn new<I: IntoIterator<Item = BigUint>>(iter: I) -> Self {
        let one = BigUint::from(1u64);
        let mut set: Vec<BigUint> = iter.into_iter().collect();
        set.sort();
        set.dedup();
        if set.len() == 0 {
            return Self::Set(vec![]);
        } else if set.len() == 1 {
            return Self::Set(vec![set[0].clone()]);
        }
        let mut inc = set[0].clone();
        for v in &set {
            if *v != inc {
                return Self::Set(set);
            }
            inc += &one;
        }
        Self::Range(set[0].clone(), set[set.len() - 1].clone())
    }
    pub fn new_unique(f: BigUint) -> Self {
        Self::Set(vec![f])
    }
    pub fn empty() -> Self {
        Self::Set(vec![])
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
    pub fn new_range(min: BigUint, max: BigUint) -> Self {
        Self::Range(min, max)
    }

    pub fn overlap(&self, other: &Self) -> bool {
        use Bound::*;
        if let (Some(a), Some(b)) = (self.unique(), other.unique()) {
            return a == b;
        }
        match (&self, other) {
            (Range(a, b), Range(c, d)) => {
                let a: &BigUint = a;
                let b: &BigUint = b;
                let min = a.max(c);
                let max = b.min(d);
                if min <= max {
                    true
                } else {
                    false
                }
            }
            (Set(a), Set(b)) => {
                let a: HashSet<&BigUint, RandomState> = HashSet::from_iter(a.iter());
                let b: HashSet<&BigUint, RandomState> = HashSet::from_iter(b.iter());
                let intersection = a.intersection(&b);
                intersection.count() != 0
            }
            (Range(min, max), Set(s)) | (Set(s), Range(min, max)) => {
                s.iter().filter(|v| &min <= v && v <= &max).count() != 0
            }
        }
    }

    /// Returns true if self changes.
    pub fn intersection(&mut self, other: &Self) -> bool {
        use Bound::*;
        let self_old = self.clone();
        match (&self, other) {
            (Range(a, b), Range(c, d)) => {
                let a: &BigUint = a;
                let b: &BigUint = b;
                let min = a.max(c);
                let max = b.min(d);
                if min <= max {
                    *self = Range(min.clone(), max.clone());
                } else {
                    *self = Set(vec![]);
                }
            }
            (Set(a), Set(b)) => {
                let a: HashSet<&BigUint, RandomState> = HashSet::from_iter(a.iter());
                let b: HashSet<&BigUint, RandomState> = HashSet::from_iter(b.iter());
                let intersection = a.intersection(&b);
                *self = Set(intersection.map(|v| (*v).clone()).collect());
            }
            (Range(min, max), Set(s)) | (Set(s), Range(min, max)) => {
                *self = Self::new(s.iter().filter(|v| &min <= v && v <= &max).cloned());
            }
        }
        let changed = self_old != *self;
        // if changed {
        //     println!("DBG {} -> {}", self_old, self);
        // }
        changed
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
    pub fn range_bits(&self) -> Option<u64> {
        if let Self::Range(start, end) = self {
            if start.is_zero() && end.count_ones() == end.bits() {
                Some(end.bits())
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
    pub fn unique(&self) -> Option<&BigUint> {
        match self {
            Bound::Set(xs) => {
                if xs.len() == 1 {
                    Some(&xs[0])
                } else {
                    None
                }
            }
            _ => None,
        }
    }
}

#[derive(Debug)]
pub struct Attrs {
    pub bound: Bound,
}

#[derive(Debug)]
pub struct Analysis<V> {
    pub vars_attrs: HashMap<V, Attrs>,
}

impl<V: Var> Analysis<V> {
    pub fn new() -> Self {
        Self {
            vars_attrs: HashMap::new(),
        }
    }

    pub fn bound_exp(&self, e: &Expr<V>) -> Option<Bound> {
        use Expr::*;
        match e {
            Var(cell) => self.vars_attrs.get(cell).map(|attrs| attrs.bound.clone()),
            Const(f) => Some(Bound::new([f.clone()])),
            _ => {
                // TODO: Implement
                None
            }
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

pub fn bound_base(p: &BigUint) -> Bound {
    Bound::new_range(BigUint::zero(), p.clone() - BigUint::one())
}

/// Try to find solutions on variables in the expression that follow a linear combination with bit-ranged variables.  Returns the list of variables with updated bounds.
/// This works by fiding the pattern `0xabc - (x + B * y + B^2 * z + ...)` where `x,y,z` are ranged
/// from 0 to B-1.
pub fn solve_ranged_linear_comb<V: Var>(
    e: &Expr<V>,
    p: &BigUint,
    analysis: &mut Analysis<V>,
) -> Vec<V> {
    use Expr::*;
    let empty = Vec::new();
    let xs = if let Sum(xs) = e {
        xs
    } else {
        return empty;
    };
    if xs.len() != 2 {
        return empty;
    }
    let mut value = if let Const(f) = &xs[0] {
        f.clone()
    } else {
        return empty;
    };
    let exp = if let Neg(e) = &xs[1] {
        e
    } else {
        return empty;
    };
    let (base, elems) = if let Some((base, elems)) = exp.get_linear_comb(p) {
        (base, elems)
    } else {
        return empty;
    };
    let base = if let Const(f) = base {
        f
    } else {
        return empty;
    };
    let base_bits = if base.count_ones() == 1 {
        base.bits() - 1
    } else {
        return empty;
    };
    let vars: Vec<&V> = elems
        .iter()
        .filter_map(|elem| if let Var(v) = elem { Some(v) } else { None })
        .collect();
    if vars.len() != elems.len() {
        return empty;
    }
    for v in &vars {
        if let Some(attrs) = analysis.vars_attrs.get(&v) {
            if let Some(range_bits) = attrs.bound.range_bits() {
                if range_bits > base_bits {
                    return empty;
                }
            } else {
                return empty;
            }
        } else {
            return empty;
        }
    }
    let mask = base - BigUint::one();
    for v in &vars {
        analysis.vars_attrs.insert(
            (*v).clone(),
            Attrs {
                bound: Bound::new_unique(value.clone() & mask.clone()),
            },
        );
        value = value >> base_bits;
    }
    assert!(value.is_zero());
    vars.iter().cloned().cloned().collect()
}

/// Try to find bounds on variables in the expression by finding values that will not satisfy the
/// polynomial identity.  Returns the list of variables with updated bounds.
pub fn find_bounds_poly<V: Var>(e: &Expr<V>, p: &BigUint, analysis: &mut Analysis<V>) -> Vec<V> {
    let (exhaustive, solutions_list) = find_solutions(e, p);
    let mut solutions = HashMap::new();
    if exhaustive {
        for (var, value) in &solutions_list {
            solutions
                .entry(var)
                .and_modify(|values: &mut Vec<BigInt>| values.push(value.clone()))
                .or_insert(vec![value.clone()]);
        }
    }
    // If there are several exhaustive solutions but they involve different variables, we can't
    // bound any variable.
    if solutions.keys().count() > 1 {
        solutions = HashMap::new();
    }
    let bound_base = bound_base(p);
    let mut update = Vec::new();
    // if analysis.vars_attrs.len() == 0 {
    //     println!("DBG1");
    // }
    for var in e.vars().iter() {
        let bound = match solutions.get(var) {
            Some(values) => Bound::new(values.into_iter().map(|c| to_biguint(c.clone(), p))),
            None => bound_base.clone(),
        };
        analysis
            .vars_attrs
            .entry(var.clone())
            .and_modify(|attrs| {
                let changed = attrs.bound.intersection(&bound);
                if changed {
                    update.push(var.clone());
                }
            })
            .or_insert_with(|| {
                update.push(var.clone());
                Attrs { bound }
            });
    }
    update
}

fn find_solutions_base<V: Var>(e: &Expr<V>) -> (bool, Vec<(V, BigInt)>) {
    use Expr::*;
    match e {
        Const(_) => (true, Vec::new()),
        Var(v) => (true, vec![(v.clone(), BigInt::zero())]),
        Neg(e) => find_solutions_base(e),
        Sum(es) => {
            // println!("DBG1");
            // for e in es {
            //     println!("  {}", e);
            // }
            let mut var: Option<V> = None;
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

fn solve_1(a: &BigUint, b: &BigUint, p: &BigUint) -> BigUint {
    // a + b*x = 0
    // x = -a * inv(b)
    mul(neg(a.clone(), p), &modinv(b.clone(), p), p)
}

pub fn find_solution_1<V: Var>(e: &Expr<V>, p: &BigUint) -> Option<(V, BigInt)> {
    use Expr::*;
    match e {
        Mul(xs) => {
            if xs.len() != 2 {
                return None;
            }
            if let (Const(b), Var(v)) = (&xs[0], &xs[1]) {
                let res = solve_1(&BigUint::zero(), &b, p);
                return Some((v.clone(), BigInt::from(res)));
            }
            return None;
        }
        Sum(xs) => {
            if xs.len() != 2 {
                return None;
            }
            if let (Const(a), Mul(ys)) = (&xs[0], &xs[1]) {
                if ys.len() != 2 {
                    return None;
                }
                if let (Const(b), Var(v)) = (&ys[0], &ys[1]) {
                    let res = solve_1(&a, &b, p);
                    return Some((v.clone(), BigInt::from(res)));
                }
            }
            return None;
        }
        _ => None,
    }
}

// Attempt to find solutions to `e(X) == 0` by matching on the pattern `(x - A)(y - B)...`.
// Returns true when the solutions returned are exhaustive.
pub fn find_solutions<V: Var>(e: &Expr<V>, p: &BigUint) -> (bool, Vec<(V, BigInt)>) {
    use Expr::*;
    if let Some(solution) = find_solution_1(e, p) {
        return (true, vec![solution]);
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

    // Return a prime for testing
    fn prime() -> BigUint {
        BigUint::parse_bytes(b"100000000000000000000000000000000", 16).unwrap()
            - BigUint::from(159u64)
    }

    #[test]
    fn test_find_solutions00() {
        let p = prime();
        for (e_str, sol_str, expected_exhaustive) in [
            ("(a - 5) * (b + 8)", vec![("a", "5"), ("b", "-8")], true),
            ("(a - 5) * (a - 7)", vec![("a", "5"), ("a", "7")], true),
            ("(-a + 5) * (-a - 7)", vec![("a", "5"), ("a", "-7")], true),
            ("(a - 3) * -(a - 4)", vec![("a", "3"), ("a", "4")], true),
            ("(a - 3) * (a + b - 4)", vec![("a", "3")], false),
            (
                "(a - 0) * (a - 1) * (a - 2) * (a - 3)",
                vec![("a", "0"), ("a", "1"), ("a", "2"), ("a", "3")],
                true,
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

            let (exhaustive, mut solutions) = find_solutions(&e, &p);
            solutions.sort();
            assert_eq!(exhaustive, expected_exhaustive, "{}", e_str);
            assert_eq!(solutions, expected_solutions, "{}", e_str);
        }
    }

    #[test]
    fn test_find_bounds_poly00() {
        let p = prime();

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

    #[test]
    fn test_carlos() {
        let p = prime();
        let poly1 = parse_expr("(x - 4) * (x - 1) * x * (x - 2) * (x - 3)").unwrap();
        let mut analysis = Analysis::new();
        find_bounds_poly(&poly1, &p, &mut analysis);
        println!("{:?}", &analysis);
    }

    #[test]
    fn test_find_bounds_poly01() {
        let p = prime();
        let poly1 = parse_expr("5*(1 - tag[1])").unwrap();
        let mut analysis = Analysis::new();
        find_bounds_poly(&poly1, &p, &mut analysis);
        println!("{:?}", &analysis);
    }
}
