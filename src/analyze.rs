use crate::expr::{Ex, Expr};

use num_bigint::{BigInt, BigUint};
use num_traits::{One, Zero};

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
}
