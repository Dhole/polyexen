use std::cmp::{Eq, Ord, Ordering, PartialEq};
use std::fmt::{self, Debug, Display, Write};
use std::ops::{Add, Mul, Neg, Sub};

trait Field: Add + Sub + Mul + Neg + Clone + Sized + Debug {
    fn q() -> Self;
    fn zero() -> Self;
    fn one() -> Self;
    fn from(v: u64) -> Self;
    fn is_zero(&self) -> bool;
    fn is_one(&self) -> bool;
}

trait Var: Clone + Debug {}

#[derive(Debug, Clone)]
enum Expr<F: Field, V: Var> {
    Const(F),
    Var(V),
    Sum(Vec<Expr<F, V>>),
    Mul(Vec<Expr<F, V>>),
}

impl<F: Field, V: Var> Add for Expr<F, V> {
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

impl<F: Field, V: Var> Sub for Expr<F, V> {
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

impl<F: Field, V: Var> Mul for Expr<F, V> {
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

impl<F: Field, V: Var> Neg for Expr<F, V> {
    type Output = Self;
    fn neg(self) -> Self {
        Expr::Const(F::q()).mul(self)
    }
}

impl<F: Field, V: Var> Ord for Expr<F, V> {
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

impl<F: Field, V: Var> PartialOrd for Expr<F, V> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<F: Field, V: Var> PartialEq for Expr<F, V> {
    fn eq(&self, _other: &Self) -> bool {
        true
    }
}

impl<F: Field, V: Var> Eq for Expr<F, V> {}

impl<F: Field + Add<Output = F> + Mul<Output = F>, V: Var> Expr<F, V> {
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
                        Sum(xs) => (c, {
                            tail.extend(xs.into_iter());
                            tail
                        }),
                        a => (c, {
                            tail.push(a);
                            tail
                        }),
                    });
                let mut r = if c.is_zero() { vec![] } else { vec![Const(c)] };
                r.extend(tail.into_iter());
                if r.len() == 1 {
                    return r.swap_remove(0);
                }
                Sum(r)
            }
            Mul(xs) => {
                let mut xs: Vec<Expr<F, V>> = xs.into_iter().map(|x| x.simplify()).collect();
                xs.sort();
                let (c, tail) = xs
                    .into_iter()
                    .fold((F::one(), Vec::new()), |(c, mut tail), x| match x {
                        Const(a) => (c * a, tail),
                        Mul(xs) => (c, {
                            tail.extend(xs.into_iter());
                            tail
                        }),
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
                if r.len() == 1 {
                    return r.swap_remove(0);
                }
                Mul(r)
            }
        }
    }
}

impl<F: Field + Display, V: Var> Expr<F, V> {
    fn is_terminal(&self) -> bool {
        use Expr::*;
        match self {
            Const(_) | Var(_) => true,
            _ => false,
        }
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
            Const(a) => write!(f, "{}", a),
            Var(a) => write!(f, "{:?}", a),
            Sum(xs) => {
                for (i, x) in xs.iter().enumerate() {
                    let parens = if x.is_terminal() {
                        false
                    } else {
                        if let Mul(_) = x {
                            false
                        } else {
                            true
                        }
                    };
                    fmt_exp(x, f, parens)?;
                    if i != xs.len() - 1 {
                        write!(f, " + ")?;
                    }
                }
                Ok(())
            }
            Mul(xs) => {
                for (i, x) in xs.iter().enumerate() {
                    let parens = if x.is_terminal() { false } else { true };
                    fmt_exp(x, f, parens)?;
                    if i != xs.len() - 1 {
                        write!(f, " * ")?;
                    }
                }
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
    fn from(v: u64) -> Self {
        Fq(v)
    }
    fn is_zero(&self) -> bool {
        self.0 == 0
    }
    fn is_one(&self) -> bool {
        self.0 == 1
    }
}

impl Var for &'static str {}

impl Add for Fq {
    type Output = Self;
    fn add(self, rhs: Self) -> Self {
        let (r, _) = self.0.overflowing_add(rhs.0);
        Fq(r)
    }
}

impl Sub for Fq {
    type Output = Self;
    fn sub(self, rhs: Self) -> Self {
        let (r, _) = self.0.overflowing_sub(rhs.0);
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
    let c = |v| -> Expr<Fq, &'static str> { Const(Fq(v)) };
    // let e = Const(Fq(2)) * Const(Fq(3)) * Var("a") + Const(Fq(5)) + Const(Fq(5)) + Var("b");
    // let e = Const(Fq(2)) * Const(Fq(3))
    //     + Const(Fq(3)) * Const(Fq(4))
    //     + Const(Fq(5))
    //     + Const(Fq(5))
    //     + Const(Fq(6))
    //     + Var("a");
    // let e = (c(2) + Var("a")) * (c(3) + Var("b")) + ((c(4) + Var("c")) * (c(5) + Var("d")));
    // let e = (c(2) - c(1)) * Var("a");
    let e: Expr<Fq, _> = -Var("a");
    println!("{:?}", e);
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
