use std::cmp::{Eq, Ord, Ordering, PartialEq};
use std::fmt::{self, Display, Write};
use std::mem::swap;
use std::ops::{Add, Mul, Neg};

trait Field: Add + Mul + Neg + Clone + Sized {
    fn q() -> Self;
    fn zero() -> Self;
    fn one() -> Self;
    fn is_zero(&self) -> bool;
    fn is_one(&self) -> bool;
}

trait Var {}

#[derive(Debug, Clone)]
enum Expr<F: Field, V> {
    Const(F),
    Var(V),
    Sum(Vec<Expr<F, V>>),
    Mul(Vec<Expr<F, V>>),
}

impl<F: Field, V> Add for Expr<F, V> {
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

impl<F: Field, V> Mul for Expr<F, V> {
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

impl<F: Field, V> Neg for Expr<F, V> {
    type Output = Self;
    fn neg(self) -> Self {
        Expr::Const(F::q()).mul(self)
    }
}

impl<F: Field, V> Ord for Expr<F, V> {
    fn cmp(&self, other: &Self) -> Ordering {
        use Expr::*;
        use Ordering::*;
        // Ordering: Const, Var, Sum, Mul
        match (self, other) {
            (Const(_a), Const(_b)) => Equal,
            (Const(_a), Var(_b)) => Less,
            (Const(_a), Sum(_b)) => Less,
            (Const(_a), Mul(_b)) => Less,
            (Var(_a), Const(_b)) => Greater,
            (Var(_a), Var(_b)) => Equal, // TODO
            (Var(_a), Sum(_b)) => Less,
            (Var(_a), Mul(_b)) => Less,
            (Sum(_a), Const(_b)) => Greater,
            (Sum(_a), Var(_b)) => Greater,
            (Sum(a), Sum(b)) => a.len().cmp(&b.len()),
            (Sum(_a), Mul(_b)) => Less,
            (Mul(_a), Const(_b)) => Greater,
            (Mul(_a), Var(_b)) => Greater,
            (Mul(_a), Sum(_b)) => Greater,
            (Mul(a), Mul(b)) => a.len().cmp(&b.len()),
        }
    }
}

impl<F: Field, V> PartialOrd for Expr<F, V> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<F: Field, V> PartialEq for Expr<F, V> {
    fn eq(&self, _other: &Self) -> bool {
        true
    }
}

impl<F: Field, V> Eq for Expr<F, V> {}

impl<F: Field + Add<Output = F> + Mul<Output = F>, V> Expr<F, V> {
    fn simplify(self) -> Self {
        use Expr::*;
        match self {
            Const(f) => Const(f),
            Var(v) => Var(v),
            Sum(xs) => {
                let mut xs: Vec<Expr<F, V>> = xs.into_iter().map(|x| x.simplify()).collect();
                xs.sort();
                let (c, tail) = xs
                    .into_iter()
                    .fold((F::zero(), Vec::new()), |(c, mut tail), x| match x {
                        Const(a) => (c + a, tail),
                        a => (c, {
                            tail.push(a);
                            tail
                        }),
                    });
                let mut r = if c.is_zero() { vec![] } else { vec![Const(c)] };
                r.extend(tail.into_iter());
                Sum(r)
            }
            Mul(xs) => {
                let mut xs: Vec<Expr<F, V>> = xs.into_iter().map(|x| x.simplify()).collect();
                xs.sort();
                let (c, tail) = xs
                    .into_iter()
                    .fold((F::one(), Vec::new()), |(c, mut tail), x| match x {
                        Const(a) => (c * a, tail),
                        a => (c, {
                            tail.push(a);
                            tail
                        }),
                    });
                let mut r = if c.is_zero() {
                    return Const(F::zero());
                } else {
                    if c.is_one() {
                        vec![]
                    } else {
                        vec![Const(c)]
                    }
                };
                r.extend(tail.into_iter());
                Mul(r)
            }
        }
    }
}

impl<F: Field + Display, V: Display> Expr<F, V> {
    fn fmt_ascii<W: Write>(&self, f: &mut W) -> fmt::Result {
        use Expr::*;
        match self {
            Const(a) => write!(f, "{}", a),
            Var(a) => write!(f, "{}", a),
            Sum(xs) => {
                write!(f, "(")?;
                for (i, x) in xs.iter().enumerate() {
                    x.fmt_ascii(f)?;
                    if i != xs.len() - 1 {
                        write!(f, " + ")?;
                    }
                }
                write!(f, ")")?;
                Ok(())
            }
            Mul(xs) => {
                write!(f, "(")?;
                for (i, x) in xs.iter().enumerate() {
                    x.fmt_ascii(f)?;
                    if i != xs.len() - 1 {
                        write!(f, " * ")?;
                    }
                }
                write!(f, ")")?;
                Ok(())
            }
        }
    }
}

#[derive(Debug, Clone)]
struct Fq(u64);

impl fmt::Display for Fq {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl Field for Fq {
    fn zero() -> Self {
        Fq(0)
    }
    fn one() -> Self {
        Fq(1)
    }
    fn q() -> Self {
        Fq(0xffffffffffffffff)
    }
    fn is_zero(&self) -> bool {
        self.0 == 0
    }
    fn is_one(&self) -> bool {
        self.0 == 1
    }
}

impl Add for Fq {
    type Output = Self;
    fn add(self, rhs: Self) -> Self {
        let (r, _) = self.0.overflowing_add(rhs.0);
        Fq(r)
    }
}

impl Mul for Fq {
    type Output = Self;
    fn mul(self, rhs: Self) -> Self {
        let (r, _) = self.0.overflowing_mul(rhs.0);
        Fq(r)
    }
}

impl Neg for Fq {
    type Output = Self;
    fn neg(self) -> Self {
        self.mul(Fq::q())
    }
}

fn main() {
    use Expr::*;
    let e = Const(Fq(2)) * Const(Fq(3)) * Var("a") + Const(Fq(5)) + Const(Fq(5)) + Var("b");
    // let e = Const(Fq(2)) * Const(Fq(3))
    //     + Const(Fq(3)) * Const(Fq(4))
    //     + Const(Fq(5))
    //     + Const(Fq(5))
    //     + Const(Fq(6))
    //     + Var("a");
    let mut s = String::new();
    e.fmt_ascii(&mut s).unwrap();
    println!("{}", s);
    s.clear();
    e.simplify().fmt_ascii(&mut s).unwrap();
    println!("{}", s);
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
// Rules
//
//
// IF (e: booly) THEN p: poly
//
// - if e(x) is truthy then p(x) == 0
//
// > e * p
//
// IF (e: bool) THEN p1: poly ELSE p2: poly
//
// - if e(x) is true then p1(x) == 0, else p2(x) == 0
//
// > e * p
// > (1 - e) * p
//
// BOOLY(e1: bool) -> booly
//
// > e1
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
// > TODO
// > (e1 - q) * (1 - (e1 - q) * w)
// $ w = inv(e1 - q)
