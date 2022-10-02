use std::ops::{Add, Mul, Neg};

trait Field: Add + Mul + Neg + Sized {
    fn q() -> Self;
}

trait Var {}

#[derive(Debug)]
enum Expr<F: Field, V> {
    Const(F),
    Var(V),
    Sum(Box<Expr<F, V>>, Box<Expr<F, V>>),
    Mul(Box<Expr<F, V>>, Box<Expr<F, V>>),
}

impl<F: Field, V> Add for Expr<F, V> {
    type Output = Self;
    fn add(self, rhs: Self) -> Self {
        use Expr::*;
        // const always on the left
        let (a, b) = match (self, rhs) {
            (Const(a), b) => (Const(a), b),
            (a, Const(b)) => (Const(b), a),
            (a, b) => (a, b),
        };
        Self::Sum(Box::new(a), Box::new(b))
    }
}

impl<F: Field, V> Mul for Expr<F, V> {
    type Output = Self;
    fn mul(self, rhs: Self) -> Self {
        use Expr::*;
        // const always on the left
        let (a, b) = match (self, rhs) {
            (Const(a), b) => (Const(a), b),
            (a, Const(b)) => (Const(b), a),
            (a, b) => (a, b),
        };
        Self::Mul(Box::new(a), Box::new(b))
    }
}

impl<F: Field, V> Neg for Expr<F, V> {
    type Output = Self;
    fn neg(self) -> Self {
        Self::Mul(Box::new(Expr::Const(F::q())), Box::new(self))
    }
}

impl<F: Field + Add<Output = F> + Mul<Output = F>, V> Expr<F, V> {
    fn simplify(self) -> Self {
        use Expr::*;
        match self {
            Const(f) => Const(f),
            Var(v) => Var(v),
            Sum(x, y) => {
                let x = (*x).simplify();
                let y = (*y).simplify();
                match (x, y) {
                    (Const(a), Const(b)) => Const(a + b),
                    (Const(c), Sum(a, b)) => match (*a, b, c) {
                        (Const(a), b, c) => Sum(Box::new(Const(a + c)), b),
                        (a, b, c) => Sum(Box::new(Const(c)), Box::new(Sum(Box::new(a), b))),
                    },
                    (x, y) => Sum(Box::new(x), Box::new(y)),
                }
            }
            Mul(x, y) => {
                let x = (*x).simplify();
                let y = (*y).simplify();
                match (x, y) {
                    (Const(a), Const(b)) => Const(a * b),
                    (Const(c), Mul(a, b)) => match (*a, b, c) {
                        (Const(a), b, c) => Mul(Box::new(Const(a * c)), b),
                        (a, b, c) => Mul(Box::new(Const(c)), Box::new(Mul(Box::new(a), b))),
                    },
                    (x, Const(a)) => Mul(Box::new(Const(a)), Box::new(x)),
                    (x, y) => Mul(Box::new(x), Box::new(y)),
                }
            }
        }
    }
}

#[derive(Debug)]
struct Fq(u64);

impl Field for Fq {
    fn q() -> Self {
        Fq(0xffffffffffffffff)
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
    println!("{:?}", e);
    println!("{:?}", e.simplify());
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
