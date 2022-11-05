use num_bigint::{BigInt, BigUint, RandBigInt, Sign};
use num_integer::Integer;
use num_traits::{One, Zero};
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

pub trait Var: Clone + Debug + Display {}

impl Var for &'static str {}
impl Var for String {}

#[derive(Debug, Clone)]
pub enum Expr<V: Var> {
    Const(BigUint),
    Var(V),
    Sum(Vec<Expr<V>>),
    Mul(Vec<Expr<V>>),
    Neg(Box<Expr<V>>),
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
        }
    }
}

impl<V: Var> PartialOrd for Expr<V> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<V: Var> PartialEq for Expr<V> {
    fn eq(&self, _other: &Self) -> bool {
        true
    }
}

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
        }
    }

    fn _simplify(self, p: &BigUint, ip: &BigInt) -> Self {
        use Expr::*;
        // p-1 == -1
        // let p_1 = p.clone() - BigUint::one();
        match self {
            Neg(e) => {
                let e = e.simplify(p);
                match e {
                    Neg(ne) => *ne, // double negate concels itself
                    e => Neg(Box::new(e)),
                }
            }
            Const(f) => Const(f),
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

impl<V: Var> Display for Expr<V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.fmt_ascii(f)
    }
}

impl<V: Var> Expr<V> {
    // sumatory terminal
    fn is_terminal(&self) -> bool {
        matches!(self, Expr::Const(_) | Expr::Var(_))
    }

    // multiplicatory terminal
    fn is_mul_terminal(&self) -> bool {
        self.is_terminal() || matches!(self, Expr::Mul(_))
    }

    fn fmt_ascii<W: Write>(&self, f: &mut W) -> fmt::Result {
        use Expr::*;
        let fmt_exp = |e: &Self, f: &mut W, parens: bool| -> fmt::Result {
            if parens {
                write!(f, "(")?;
            }
            e.fmt_ascii(f)?;
            if parens {
                write!(f, ")")?;
            }
            Ok(())
        };
        match self {
            Neg(a) => {
                write!(f, "-")?;
                let parens = !a.is_terminal();
                fmt_exp(a, f, parens)?;
                Ok(())
            }
            Const(c) => write!(f, "{}", c),
            Var(v) => write!(f, "{}", v),
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
        let mut s = String::new();
        e.fmt_ascii(&mut s).unwrap();
        println!("e: {}", s);

        let e = e.clone().normalize(&p);
        s.clear();
        e.fmt_ascii(&mut s).unwrap();
        println!("e.normalize: {}", s);

        let e = e.simplify(&p);
        println!("raw e.normalize: {:?}", e);
        s.clear();
        e.fmt_ascii(&mut s).unwrap();
        println!("e.simplify: {}", s);

        let e = e.normalize(&p);
        s.clear();
        e.fmt_ascii(&mut s).unwrap();
        println!("e.normalize: {}", s);
    }

    #[test]
    fn test_fmt_ascii() {
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
            let mut s = String::new();
            exp.fmt_ascii(&mut s).unwrap();
            assert_eq!(s.as_str(), exp_fmt);
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
                let mut s1 = String::new();
                e1.fmt_ascii(&mut s1).unwrap();
                let mut s2 = String::new();
                e2.fmt_ascii(&mut s2).unwrap();
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
    use super::*;
    use crate::parser::parse;

    use rand::SeedableRng;
    use rand_chacha::ChaCha20Rng;

    #[test]
    fn test_test_eq() {
        let mut rng = ChaCha20Rng::seed_from_u64(0);
        for (e1_str, e2_str) in [("(a - 5)*(a - 7)", "a*a - a*7 - a*5 + 35")] {
            let e1 = parse(e1_str).unwrap();
            let e2 = parse(e2_str).unwrap();
            assert!(e1.test_eq(&mut rng, &e2))
        }
    }
}

// Types
//
//
// bool: [0, 1].
// - 0: False
// - 1: True
//
// booly: [0, q]
// - 0: False
// - 1-q: True
//
// range(a, b): [a, b]
//
// u8, byte: range(0, 0xff)
//
// u16: range(0, 0xffff)
//
//
// Rules
//
//
// BOOLY(e: expr) -> booly
//
// - if e(x) == 0 then False else True
//
// IF (b: booly) THEN e: expr
//
// - if b(x) is truthy then BOOLY(e(x))
//
// > e * p
//
// IF (e: bool) THEN e1: expr ELSE e2: expr
//
// - if e(x) is true then e1, else e2
//
// > e * p
// > (1 - e) * p
//
// e1: booly AND e2:booly -> booly
//
// > e1 * e2
//
// e1: bool AND e2:bool -> bool
//
// > e1 * e2
//
// e1: bool OR e2:bool -> bool
//
// > e1 + e2 - e1 * e2
//
// e1: expr == q: const -> bool
//
// > (1 - (e1 - q) * w)
// % (e1 - q) * (1 - (e1 - q) * w)
// $ w := inv(e1 - q) if (e1 - q) != 0
// $ w := 0 if (e1 - q) == 0
//
// not(e: expr in S) -> booly
//   for S = {s1, s2, ..., sn}
//
// (e - s1) * (e - s2) * ... * (e - sn)
//
// CONSTRAIN(not(e: booly))
//
// - e(x) == false
//
// > e == 0
