use halo2_proofs::{
    halo2curves::group::ff::{Field, PrimeField},
    plonk::Expression,
};
use num_bigint::{BigInt, BigUint, RandBigInt, Sign};
use num_integer::Integer;
use num_traits::{One, ToPrimitive, Zero};
use rand::Rng;
use std::cmp::{Eq, Ord, Ordering, PartialEq};
use std::collections::{HashMap, HashSet};
use std::fmt::{self, Debug, Display, Write};
use std::hash::Hash;
use std::ops::{Add, Mul, Neg, Sub};

// trait Field: Add + Sub + Mul + Neg + Clone + Sized + Debug {
//     fn q() -> Self;
//     fn zero() -> Self;
//     fn one() -> Self;
//     fn from(v: u64) -> Self;
//     fn is_zero(&self) -> bool;
//     fn is_one(&self) -> bool;
// }

pub trait Var: Clone + Debug + PartialEq {}

impl Var for &'static str {}
impl Var for String {}

#[derive(Debug, Clone, PartialEq)]
pub enum Expr<V: Var> {
    Const(BigUint),
    Var(V),
    Sum(Vec<Expr<V>>),
    Mul(Vec<Expr<V>>),
    Neg(Box<Expr<V>>),
    Pow(Box<Expr<V>>, BigUint),
}

pub type Ex = Expr<String>;

pub fn get_field_p<F: Field + PrimeField<Repr = [u8; 32]>>() -> BigUint {
    let p_1 = F::zero() - F::one();
    let p_1 = BigUint::from_bytes_le(&p_1.to_repr()[..]);
    p_1 + 1u64
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum ColumnKind {
    Witness,
    Public,
    Fixed,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Column {
    pub kind: ColumnKind,
    pub index: usize,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum PlonkVar {
    ColumnQuery { column: Column, rotation: i32 },
    Challenge { index: usize, phase: usize },
}

impl Var for PlonkVar {}

impl Display for PlonkVar {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use ColumnKind::*;
        use PlonkVar::*;
        match self {
            ColumnQuery {
                column: Column { kind, index },
                rotation,
            } => {
                write!(
                    f,
                    "{}{:02}",
                    match kind {
                        Witness => "w",
                        Public => "p",
                        Fixed => "f",
                    },
                    index
                )?;
                if *rotation != 0 {
                    write!(f, "[{}]", rotation)?;
                }
            }
            Challenge { index, phase } => write!(f, "ch{}_{}", index, phase)?,
        }
        Ok(())
    }
}

impl<F: PrimeField<Repr = [u8; 32]>> From<&Expression<F>> for Expr<PlonkVar> {
    fn from(e: &Expression<F>) -> Self {
        use Expression::*;
        match e {
            Constant(c) => Expr::Const(BigUint::from_bytes_le(&c.to_repr()[..])),
            Selector(_) => unreachable!("selector exoression is unsupported"),
            Fixed(query) => Expr::Var(PlonkVar::ColumnQuery {
                column: Column {
                    kind: ColumnKind::Fixed,
                    index: query.column_index(),
                },
                rotation: query.rotation().0,
            }),
            Advice(query) => Expr::Var(PlonkVar::ColumnQuery {
                column: Column {
                    kind: ColumnKind::Witness,
                    index: query.column_index(),
                },
                rotation: query.rotation().0,
            }),
            Instance(query) => Expr::Var(PlonkVar::ColumnQuery {
                column: Column {
                    kind: ColumnKind::Public,
                    index: query.column_index(),
                },
                rotation: query.rotation().0,
            }),
            Challenge(challenge) => Expr::Var(PlonkVar::Challenge {
                index: challenge.index(),
                phase: challenge.phase() as usize,
            }),
            Negated(e) => -Self::from(&**e),
            Sum(e1, e2) => Self::from(&**e1) + Self::from(&**e2),
            Product(e1, e2) => Self::from(&**e1) * Self::from(&**e2),
            Scaled(e, c) => {
                Expr::Const(BigUint::from_bytes_le(&c.to_repr()[..])) * Self::from(&**e)
            }
        }
    }
}

fn rand<R: Rng>(rng: &mut R, p: &BigUint) -> BigUint {
    rng.gen_biguint_below(p)
}

const VARS: &str = "abcdefghijklmnopqrstuvwxyz";

impl Expr<&'static str> {
    pub fn rand_depth<R: Rng>(rng: &mut R, p: &BigUint, depth: usize) -> Self {
        use Expr::*;
        const MAX_ELEMS: usize = 8;
        let case_max = if depth > 0 { 4 } else { 1 };
        let case: u8 = rng.gen_range(0..=case_max);
        match case {
            0 => Const(rand(rng, p)),
            1 => {
                let i = rng.gen_range(0..26);
                Var(&VARS[i..i + 1])
            }
            2 => {
                let mut v = Vec::new();
                for _ in 0..rng.gen_range(2..MAX_ELEMS) {
                    v.push(Expr::rand_depth(rng, p, depth - 1));
                }
                Sum(v)
            }
            3 => {
                let mut v = Vec::new();
                for _ in 0..rng.gen_range(2..MAX_ELEMS) {
                    v.push(Expr::rand_depth(rng, p, depth - 1));
                }
                Mul(v)
            }
            4 => Neg(Box::new(Expr::rand_depth(rng, p, depth - 1))),
            _ => unreachable!(),
        }
    }
    pub fn rand<R: Rng>(rng: &mut R, p: &BigUint) -> Self {
        Expr::rand_depth(rng, p, 4)
    }
}

impl<V: Var> Add for Expr<V> {
    type Output = Self;
    fn add(self, rhs: Self) -> Self {
        use Expr::*;
        match self {
            Sum(mut xs) => {
                xs.push(rhs);
                Sum(xs)
            }
            e => Sum(vec![e, rhs]),
        }
    }
}

impl<V: Var> Sub for Expr<V> {
    type Output = Self;
    fn sub(self, rhs: Self) -> Self {
        use Expr::*;
        match self {
            Sum(mut xs) => {
                xs.push(rhs.neg());
                Sum(xs)
            }
            e => Sum(vec![e, rhs.neg()]),
        }
    }
}

impl<V: Var> Mul for Expr<V> {
    type Output = Self;
    fn mul(self, rhs: Self) -> Self {
        use Expr::*;
        match self {
            Mul(mut xs) => {
                xs.push(rhs);
                Mul(xs)
            }
            e => Mul(vec![e, rhs]),
        }
    }
}

impl<V: Var> Neg for Expr<V> {
    type Output = Self;
    fn neg(self) -> Self {
        Expr::Neg(Box::new(self))
    }
}

impl<V: Var> Ord for Expr<V> {
    fn cmp(&self, other: &Self) -> Ordering {
        use Expr::*;
        use Ordering::*;
        // Ordering: Const, Var, Sum, Mul
        match (self, other) {
            (Const(_), Const(_)) => Equal,
            (Const(_), Var(_)) => Less,
            (Const(_), Sum(_)) => Less,
            (Const(_), Mul(_)) => Less,
            (Const(_), Neg(e)) => self.cmp(e),
            (Var(_), Const(_)) => Greater,
            (Var(_), Var(_)) => Equal, // TODO
            (Var(_), Sum(_)) => Less,
            (Var(_), Mul(_)) => Less,
            (Var(_), Neg(e)) => self.cmp(e),
            (Sum(_), Const(_)) => Greater,
            (Sum(_), Var(_)) => Greater,
            (Sum(a), Sum(b)) => a.len().cmp(&b.len()),
            (Sum(_), Mul(_)) => Less,
            (Sum(_), Neg(e)) => self.cmp(e),
            (Mul(_), Const(_)) => Greater,
            (Mul(_), Var(_)) => Greater,
            (Mul(_), Sum(_)) => Greater,
            (Mul(a), Mul(b)) => a.len().cmp(&b.len()),
            (Mul(_), Neg(e)) => self.cmp(e),
            (Neg(e), Const(_)) => (**e).cmp(other),
            (Neg(e), Var(_)) => (**e).cmp(other),
            (Neg(e), Sum(_)) => (**e).cmp(other),
            (Neg(e), Mul(_)) => (**e).cmp(other),
            (Neg(e1), Neg(e2)) => (**e1).cmp(e2),
            _ => Equal,
        }
    }
}

impl<V: Var> PartialOrd for Expr<V> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

// impl<V: Var> PartialEq for Expr<V> {
//     fn eq(&self, _other: &Self) -> bool {
//         true
//     }
// }

impl<V: Var> Eq for Expr<V> {}

// Keep n between -(p-1) and (p-1) after an addition or subtraction operation.
fn norm(n: BigInt, p: &BigInt) -> BigInt {
    if &n >= p {
        n - p
    } else if n <= -p {
        n + p
    } else {
        n
    }
}

fn iadd(lhs: BigInt, rhs: BigUint, p: &BigInt) -> BigInt {
    let r = lhs + BigInt::from(rhs);
    norm(r, p)
}

fn isub(lhs: BigInt, rhs: BigUint, p: &BigInt) -> BigInt {
    let r = lhs - BigInt::from(rhs);
    norm(r, p)
}

fn add(lhs: BigUint, rhs: BigUint, p: &BigUint) -> BigUint {
    let r = lhs + rhs;
    if &r >= p {
        r - p
    } else {
        r
    }
}

fn neg(n: BigUint, p: &BigUint) -> BigUint {
    p - n
}

fn mul(lhs: BigUint, rhs: &BigUint, p: &BigUint) -> BigUint {
    (lhs * rhs).mod_floor(p)
}

impl<V: Var + Eq + Hash + Ord> Expr<V> {
    pub fn eval(&self, p: &BigUint, vars: &HashMap<V, BigUint>) -> BigUint {
        use Expr::*;
        match self {
            Neg(e) => neg((*e).eval(p, vars), p),
            Const(f) => f.clone(),
            Var(v) => vars.get(v).unwrap().clone(),
            Sum(es) => {
                let mut res = BigUint::zero();
                for e in es.iter().map(|e| e.eval(p, vars)) {
                    res = add(res, e, p);
                }
                res
            }
            Mul(es) => {
                let mut res = BigUint::one();
                for e in es.iter().map(|e| e.eval(p, vars)) {
                    res = mul(res, &e, p);
                }
                res
            }
            Pow(e, f) => {
                let b = e.eval(p, vars);
                let mut res = BigUint::one();
                let exp: u32 = f.to_u32().expect("exponent too big");
                // TODO: Implement efficient expmod
                for _ in 0..exp {
                    res = mul(res, &b, p);
                }
                res
            }
        }
    }

    fn _simplify(self, p: &BigUint, ip: &BigInt) -> Self {
        use Expr::*;
        // p-1 == -1
        // let p_1 = p.clone() - BigUint::one();
        match self {
            Pow(e, f) => {
                let e = e.simplify(p);
                Pow(Box::new(e), f)
            }
            Neg(e) => {
                let e = e.simplify(p);
                match e {
                    Neg(ne) => *ne, // double negate concels itself
                    e => Neg(Box::new(e)),
                }
            }
            Const(f) => match (f.count_ones(), f.trailing_zeros()) {
                // Express values greater-equal than 2^8 as 2^n
                (1, Some(n)) if n >= 8 => {
                    Pow(Box::new(Const(BigUint::from(2u32))), BigUint::from(n))
                }
                _ => Const(f),
            },
            Var(v) => Var(v),
            Sum(es) => {
                let mut xs: Vec<Expr<V>> = Vec::new();
                for x in es.into_iter().map(|x| x.simplify(p)) {
                    match x {
                        Sum(es) => xs.extend(es.into_iter()),
                        e => xs.push(e),
                    }
                }
                xs.sort();
                let mut c = BigInt::zero();
                let mut tail = Vec::new();
                for x in xs {
                    match x {
                        Neg(e) => match *e {
                            Const(a) => c = isub(c, a, ip),
                            a => tail.push(Neg(Box::new(a))),
                        },
                        Const(a) => c = iadd(c, a, ip),
                        a => tail.push(a),
                    }
                }
                let mut r = if c.is_zero() {
                    vec![]
                } else {
                    let (sign, c) = c.into_parts();
                    if sign == Sign::Minus {
                        vec![Neg(Box::new(Const(c)))]
                    } else {
                        vec![Const(c)]
                    }
                };
                r.extend(tail.into_iter());
                match r.len() {
                    0 => Const(BigUint::zero()),
                    1 => r.swap_remove(0),
                    _ => Sum(r),
                }
            }
            Mul(es) => {
                // TODO: get Pow's out of Mul elements
                let mut xs: Vec<Expr<V>> = Vec::new();
                let mut neg = false;
                for x in es.into_iter().map(|x| x.simplify(p)) {
                    match x {
                        Neg(e) => {
                            neg ^= true;
                            match *e {
                                Mul(es) => xs.extend(es.into_iter()),
                                ne => xs.push(ne),
                            }
                        }
                        Mul(es) => xs.extend(es.into_iter()),
                        e => xs.push(e),
                    }
                }
                xs.sort();
                let mut c = BigUint::one();
                let mut tail = Vec::new();
                for x in xs {
                    match x {
                        Const(a) => c = mul(c, &a, p),
                        a => tail.push(a),
                    }
                }
                let mut r = if c.is_zero() {
                    return Const(BigUint::zero());
                } else if c.is_one() {
                    vec![]
                } else {
                    vec![Const(c)]
                };
                r.extend(tail.into_iter());
                let m = if r.len() == 1 {
                    r.swap_remove(0)
                } else {
                    Mul(r)
                };
                if neg {
                    Neg(Box::new(m))
                } else {
                    m
                }
            }
        }
    }

    pub fn simplify(self, p: &BigUint) -> Self {
        let ip = BigInt::from(p.clone());
        self._simplify(p, &ip)
    }

    fn _normalize(self, p: &BigUint) -> Self {
        use Expr::*;
        // p-1 == -1
        let p_1 = p.clone() - BigUint::one();
        match self {
            Neg(e) => Mul(vec![Const(p_1), *e]),
            Sum(xs) => {
                let xs: Vec<Expr<V>> = xs.into_iter().map(|x| x.normalize(p)).collect();
                Sum(xs)
            }
            Mul(xs) => {
                let mut xs: Vec<Expr<V>> = xs.into_iter().map(|x| x.normalize(p)).collect();
                xs.sort();
                let mut iter = xs.into_iter();
                let mul_acc = iter.next().unwrap();
                let mut mul_acc = match mul_acc {
                    Sum(xs) => xs,
                    e => vec![e],
                };
                for next in iter {
                    let e = match next {
                        Sum(xs) => xs,
                        e => vec![e],
                    };
                    let mut acc = Vec::new();
                    for a in mul_acc.into_iter() {
                        for b in &e {
                            acc.push(Mul(vec![a.clone(), b.clone()]));
                        }
                    }
                    mul_acc = acc;
                }
                Sum(mul_acc)
            }
            _ => self,
        }
    }

    pub fn normalize(self, p: &BigUint) -> Self {
        self.simplify(p)._normalize(p).simplify(p)
    }

    fn _vars(&self, vars: &mut HashSet<V>) {
        use Expr::*;
        match self {
            Const(_) => {}
            Var(v) => {
                vars.insert(v.clone());
            }
            Neg(e) => e._vars(vars),
            Pow(e, _) => e._vars(vars),
            Sum(es) => es.iter().for_each(|e| e._vars(vars)),
            Mul(es) => es.iter().for_each(|e| e._vars(vars)),
        }
    }

    pub fn vars(&self) -> HashSet<V> {
        let mut vars = HashSet::new();
        self._vars(&mut vars);
        vars
    }

    pub fn test_eq<R: Rng>(&self, rng: &mut R, other: &Self) -> bool {
        let p = BigUint::parse_bytes(b"100000000000000000000000000000000", 16).unwrap()
            - BigUint::from(159u64);
        let e1_vars = self.vars();
        let e2_vars = other.vars();
        let mut vars_vec = e1_vars.union(&e2_vars).into_iter().collect::<Vec<_>>();
        vars_vec.sort();
        let vars = vars_vec
            .into_iter()
            .map(|v| (v.clone(), rand(rng, &p)))
            .collect();
        let e1_eval = self.eval(&p, &vars);
        let e2_eval = other.eval(&p, &vars);
        e1_eval == e2_eval
    }
}

impl<V: Var + Display> Display for Expr<V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.fmt_ascii(f, &mut |f: &mut fmt::Formatter<'_>, v: &V| {
            write!(f, "{}", v)
        })
    }
}

impl<V: Var> Expr<V> {
    // sumatory terminal
    fn is_terminal(&self) -> bool {
        matches!(self, Expr::Const(_) | Expr::Var(_) | Expr::Pow(_, _))
    }

    // multiplicatory terminal
    fn is_mul_terminal(&self) -> bool {
        self.is_terminal() || matches!(self, Expr::Mul(_))
    }

    pub fn fmt_ascii<W: Write, FV>(&self, f: &mut W, fmt_var: &mut FV) -> fmt::Result
    where
        FV: FnMut(&mut W, &V) -> fmt::Result,
    {
        use Expr::*;
        let mut fmt_exp = |e: &Self, f: &mut W, parens: bool| -> fmt::Result {
            if parens {
                write!(f, "(")?;
            }
            e.fmt_ascii(f, fmt_var)?;
            if parens {
                write!(f, ")")?;
            }
            Ok(())
        };
        match self {
            Neg(e) => {
                write!(f, "-")?;
                let parens = !e.is_terminal();
                fmt_exp(e, f, parens)?;
                Ok(())
            }
            Pow(e, c) => {
                let parens = !e.is_terminal();
                fmt_exp(e, f, parens)?;
                write!(f, "^{}", c)
            }
            Const(c) => write!(f, "{}", c),
            Var(v) => fmt_var(f, v),
            Sum(es) => {
                for (i, e) in es.iter().enumerate() {
                    let (neg, e) = if let Neg(e) = e {
                        (true, &**e)
                    } else {
                        (false, e)
                    };
                    if i == 0 {
                        if neg {
                            write!(f, "-")?;
                        }
                    } else if neg {
                        write!(f, " - ")?;
                    } else {
                        write!(f, " + ")?;
                    }
                    let parens = !e.is_mul_terminal();
                    fmt_exp(e, f, parens)?;
                }
                Ok(())
            }
            Mul(es) => {
                for (i, e) in es.iter().enumerate() {
                    let parens = !e.is_terminal();
                    fmt_exp(e, f, parens)?;
                    if i != es.len() - 1 {
                        write!(f, "*")?;
                    }
                }
                Ok(())
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use Expr::*;

    use rand::SeedableRng;
    use rand_chacha::ChaCha20Rng;

    fn c(v: u64) -> Expr<&'static str> {
        Const(BigUint::from(v))
    }

    #[test]
    fn test_scratch() {
        let p = BigUint::from(0x1_00_00u64);
        // let e = c(2) * c(3) * Var("a") + c(5) + c(5) + Var("b");
        // let e = c(2) * c(3) + c(3) * c(4) + c(5) + c(5) + c(6) + Var("a");
        // let e = (c(2) + Var("a")) * (c(3) + Var("b")) + ((c(4) + Var("c")) * (c(5) + Var("d")));
        // let e = (c(2) - c(1)) * Var("a");
        // let e = (c(1) - c(2)) * Var("a");
        // let e = (c(0xffff)) - (c(0xff00) - (-c(123))) * Var("a");
        // let e = Var("a") - Var("b");
        // let e = c(5) * (Var("a") * (c(1) - c(2)) * Var("b") + Var("c"));
        let mut rng = ChaCha20Rng::seed_from_u64(9);
        let e = Expr::rand(&mut rng, &p);
        println!("raw e: {:?}", e);
        println!("e: {}", e);

        let e = e.clone().normalize(&p);
        println!("e.normalize: {}", e);

        let e = e.simplify(&p);
        println!("raw e.normalize: {:?}", e);
        println!("e.simplify: {}", e);

        let e = e.normalize(&p);
        println!("e.normalize: {}", e);
    }

    #[test]
    fn test_display() {
        #[rustfmt::skip]
        let tests = vec![
            (
                c(2) * c(3) * Var("a") + c(5) + c(5) + Var("b"),
                "2*3*a + 5 + 5 + b",
            ),
            (
                (c(2) + Var("a")) * (c(3) + Var("b")) + ((c(4) + Var("c")) * (c(5) + Var("d"))),
                "(2 + a)*(3 + b) + (4 + c)*(5 + d)",
            ),
            (
                -(c(2) - Var("a")),
                "-(2 - a)"
            ),
            (
                (-c(1) + c(2)),
                "-1 + 2"
            ),
        ];
        for (exp, exp_fmt) in tests {
            assert_eq!(format!("{}", exp).as_str(), exp_fmt);
        }
    }

    #[test]
    fn test_simplify() {
        let p = BigUint::from(0x10000u64 - 15);
        let vars: HashMap<&'static str, BigUint> = {
            let mut rng = ChaCha20Rng::seed_from_u64(0);
            (0..26)
                .map(|i| (&VARS[i..i + 1], rand(&mut rng, &p)))
                .collect()
        };
        let mut rng = ChaCha20Rng::seed_from_u64(0);
        for i in 0..1024 {
            let e1 = Expr::rand(&mut rng, &p);
            let e2 = e1.clone().simplify(&p);
            let eval1 = e1.eval(&p, &vars);
            let eval2 = e2.eval(&p, &vars);
            if eval1 != eval2 {
                let s1 = format!("{}", e1);
                let s2 = format!("{}", e2);
                println!("{} e1: {}", i, s1);
                println!("{} e2: {}", i, s2);
            }
            assert_eq!(eval1, eval2);
        }
    }

    #[test]
    fn test_normalize() {
        let p = BigUint::from(0x10000u64 - 15);
        let vars: HashMap<&'static str, BigUint> = {
            let mut rng = ChaCha20Rng::seed_from_u64(0);
            (0..26)
                .map(|i| (&VARS[i..i + 1], rand(&mut rng, &p)))
                .collect()
        };
        let mut rng = ChaCha20Rng::seed_from_u64(0);
        for _i in 0..1024 {
            let e1 = Expr::rand_depth(&mut rng, &p, 3);
            let e2 = e1.clone().normalize(&p);
            let eval1 = e1.eval(&p, &vars);
            let eval2 = e2.eval(&p, &vars);
            assert_eq!(eval1, eval2);
        }
    }

    #[test]
    fn test_vars() {
        let e = c(2) * c(3) * Var("a") + c(5) + c(5) + Var("b") + (Var("b") + c(3)) * Var("c");
        let vars = e.vars();
        let mut vars_vec = vars.into_iter().collect::<Vec<_>>();
        vars_vec.sort();
        assert_eq!(vars_vec, vec!["a", "b", "c"])
    }
}

#[cfg(test)]
mod tests_with_parser {
    // use super::*;
    use crate::parser::parse_expr;

    use rand::SeedableRng;
    use rand_chacha::ChaCha20Rng;

    #[test]
    fn test_test_eq() {
        let mut rng = ChaCha20Rng::seed_from_u64(0);
        for (e1_str, e2_str) in [("(a - 5)*(a - 7)", "a*a - a*7 - a*5 + 35")] {
            let e1 = parse_expr(e1_str).unwrap();
            let e2 = parse_expr(e2_str).unwrap();
            assert!(e1.test_eq(&mut rng, &e2))
        }
    }
}
