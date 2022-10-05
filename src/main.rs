use num_bigint::{BigInt, BigUint, Sign};
use num_integer::Integer;
use num_traits::{One, Zero};
use std::cmp::{Eq, Ord, Ordering, PartialEq};
use std::fmt::{self, Debug, Display, Write};
use std::ops::{Add, Mul, Neg, Sub};

// trait Field: Add + Sub + Mul + Neg + Clone + Sized + Debug {
//     fn q() -> Self;
//     fn zero() -> Self;
//     fn one() -> Self;
//     fn from(v: u64) -> Self;
//     fn is_zero(&self) -> bool;
//     fn is_one(&self) -> bool;
// }

trait Var: Clone + Debug + Display {}

impl Var for &'static str {}

#[derive(Debug, Clone)]
enum Expr<V: Var> {
    Const(BigUint),
    Var(V),
    Sum(Vec<Expr<V>>),
    Mul(Vec<Expr<V>>),
    Neg(Box<Expr<V>>),
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
    } else if -&n <= -p {
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

fn mul(lhs: BigUint, rhs: &BigUint, p: &BigUint) -> BigUint {
    (lhs * rhs).mod_floor(p)
}

impl<V: Var> Expr<V> {
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
            Sum(xs) => {
                let mut xs: Vec<Expr<V>> = xs.into_iter().map(|x| x.simplify(p)).collect();
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
                        Sum(xs) => tail.extend(xs.into_iter()),
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
                let s = match r.len() {
                    0 => Const(BigUint::zero()),
                    1 => r.swap_remove(0),
                    _ => Sum(r),
                };
                s
            }
            Mul(xs) => {
                let mut xs: Vec<Expr<V>> = xs.into_iter().map(|x| x.simplify(p)).collect();
                xs.sort();
                let mut neg = false;
                let mut c = BigUint::one();
                let mut tail = Vec::new();
                for x in xs {
                    let (x_is_neg, x) = match x {
                        Neg(e) => (true, *e),
                        e => (false, e),
                    };
                    neg = neg ^ x_is_neg;
                    match x {
                        Const(a) => c = mul(c, &a, p),
                        Mul(xs) => tail.extend(xs.into_iter()),
                        a => tail.push(a),
                    }
                }
                let mut r = if c.is_zero() {
                    return Const(BigUint::zero());
                } else {
                    if c.is_one() {
                        vec![]
                    } else {
                        vec![Const(c)]
                    }
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

    fn simplify(self, p: &BigUint) -> Self {
        let ip = BigInt::from(p.clone());
        self._simplify(p, &ip)
    }

    fn normalize(self, p: &BigUint) -> Self {
        todo!();
    }
}

impl<V: Var> Expr<V> {
    // sumatory terminal
    fn is_terminal(&self) -> bool {
        use Expr::*;
        match self {
            Const(_) | Var(_) => true,
            _ => false,
        }
    }

    // multiplicatory terminal
    fn is_mul_terminal(&self) -> bool {
        if self.is_terminal() {
            true
        } else {
            if let Expr::Mul(_) = self {
                true
            } else {
                false
            }
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
            Neg(a) => {
                write!(f, "-")?;
                fmt_exp(a, f, false)?;
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
                    if i != 0 {
                        if neg {
                            write!(f, " - ")?;
                        } else {
                            write!(f, " + ")?;
                        }
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
                        write!(f, " * ")?;
                    }
                }
                Ok(())
            }
        }
    }
}

fn main() {
    use Expr::*;
    let c = |v: u64| -> Expr<&'static str> { Const(BigUint::from(v)) };
    let p = BigUint::from(0x1_00_00u64);
    // let e = c(2) * c(3) * Var("a") + c(5) + c(5) + Var("b");
    // let e = c(2) * c(3) + c(3) * c(4) + c(5) + c(5) + c(6) + Var("a");
    // let e = (c(2) + Var("a")) * (c(3) + Var("b")) + ((c(4) + Var("c")) * (c(5) + Var("d")));
    // let e = (c(2) - c(1)) * Var("a");
    // let e = (c(1) - c(2)) * Var("a");
    // let e = (c(0xffff)) - (c(0xff00) - (-c(123))) * Var("a");
    // let e = Var("a") - Var("b");
    let e = c(5) * (Var("a") * (c(1) - c(2)) * Var("b") + Var("c"));
    println!("{:?}", e);
    let mut s = String::new();
    e.fmt_ascii(&mut s).unwrap();
    println!("{}", s);
    s.clear();
    let e = e.simplify(&p);
    println!("{:?}", e);
    e.fmt_ascii(&mut s).unwrap();
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
