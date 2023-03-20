use crate::expr::{Ex, Expr};
use num_traits::ToPrimitive;

use num_bigint::BigUint;

extern crate pest;

use pest::{error::Error, Parser};

#[derive(Parser)]
#[grammar = "grammar.pest"]
struct ExprParser;
use pest::{iterators::Pairs, pratt_parser::PrattParser};

lazy_static! {
    static ref PRATT_PARSER: PrattParser<Rule> = {
        use pest::pratt_parser::{Assoc::*, Op};
        use Rule::*;

        PrattParser::new()
            .op(Op::infix(add, Left) | Op::infix(subtract, Left))
            .op(Op::infix(multiply, Left))
            .op(Op::infix(exp, Left))
    };
}

pub fn parse_expr_pairs(expression: Pairs<Rule>) -> Ex {
    use Expr::*;
    PRATT_PARSER
        .map_primary(|primary| match primary.as_rule() {
            Rule::dec => (
                Const(BigUint::parse_bytes(primary.as_str().as_bytes(), 10).unwrap()),
                true,
            ),
            Rule::hex => (
                Const(BigUint::parse_bytes(primary.as_str().as_bytes(), 16).unwrap()),
                true,
            ),
            Rule::var => (Var(primary.as_str().to_string()), true),
            Rule::neg => (Neg(Box::new(parse_expr_pairs(primary.into_inner()))), true),
            Rule::expr => (parse_expr_pairs(primary.into_inner()), false),
            _ => unreachable!(),
        })
        // lcont and rcont tell wether the lhs and rhs terms belong to the same expr or not
        .map_infix(|(lhs, lcont), op, (rhs, rcont)| {
            (
                match op.as_rule() {
                    Rule::add => match (lhs, rhs, lcont & rcont) {
                        (Sum(mut es), rhs, true) => {
                            es.push(rhs);
                            Sum(es)
                        }
                        (Sum(mut lhs_es), Mul(rhs_es), _) => {
                            lhs_es.push(Mul(rhs_es));
                            Sum(lhs_es)
                        }
                        (lhs, rhs, _) => Sum(vec![lhs, rhs]),
                    },
                    Rule::subtract => match (lhs, rhs, lcont & rcont) {
                        (Sum(mut es), rhs, true) => {
                            es.push(Neg(Box::new(rhs)));
                            Sum(es)
                        }
                        (lhs, rhs, _) => Sum(vec![lhs, Neg(Box::new(rhs))]),
                    },
                    Rule::multiply => match (lhs, rhs, lcont & rcont) {
                        (Mul(mut es), rhs, true) => {
                            es.push(rhs);
                            Mul(es)
                        }
                        (Mul(mut lhs_es), Sum(rhs_es), _) => {
                            lhs_es.push(Sum(rhs_es));
                            Mul(lhs_es)
                        }
                        (lhs, rhs, _) => Mul(vec![lhs, rhs]),
                    },
                    Rule::exp => {
                        let rhs = match rhs {
                            Const(c) => c.to_u32().expect("exponent fits in u32"),
                            _ => unreachable!(),
                        };
                        Pow(Box::new(lhs), rhs)
                    }
                    _ => unreachable!(),
                },
                true,
            )
        })
        .parse(expression)
        .0
}

pub fn parse_expr(src: &str) -> Result<Ex, Error<Rule>> {
    let r = ExprParser::parse(Rule::expr, src)?;
    Ok(parse_expr_pairs(r))
}

#[cfg(test)]
mod tests {
    use super::*;
    use Expr::*;

    fn c(v: u64) -> Expr<String> {
        Const(BigUint::from(v))
    }

    #[test]
    fn test_parse() {
        for (e_str, e_expected) in [
            ("123", c(123)),
            ("-123", Neg(Box::new(c(123)))),
            ("0x42", c(0x42)),
            ("-0x42", Neg(Box::new(c(0x42)))),
            ("3 + 5", c(3) + c(5)),
            ("3 + 5 * a", c(3) + c(5) * Var("a".to_string())),
            ("(3 + 5) + 2", Sum(vec![c(3) + c(5), c(2)])),
            ("-(1 + 2)", Neg(Box::new(c(1) + c(2)))),
            (
                "(9 + 0) * (9 + 1) * (9 + 2)",
                Mul(vec![
                    Sum(vec![c(9), c(0)]),
                    Sum(vec![c(9), c(1)]),
                    Sum(vec![c(9), c(2)]),
                ]),
            ),
            (
                "9 * 0 + 9 * 1 + 9 * 2 - 9 * 3",
                Sum(vec![
                    Mul(vec![c(9), c(0)]),
                    Mul(vec![c(9), c(1)]),
                    Mul(vec![c(9), c(2)]),
                    Neg(Box::new(Mul(vec![c(9), c(3)]))),
                ]),
            ),
        ] {
            let e = parse_expr(e_str).unwrap();
            assert_eq!(e, e_expected, "{}", e_str);
        }
        // let r = ExprParser::parse(Rule::expr, "-(-1 + 2)");
        // dbg!(&r);
        // let e = parse_expr_pairs(r.unwrap());
        // println!("{:?}", e);
        // println!("{}", e);
    }

    #[test]
    fn test_parser_bug_1() {
        let e1_str = "f05*w77*w78*w79*w80*(1 - w76)*(w26 - w26[-1]*2^0 + w25[-1]*2^1 + w24[-1]*2^2 + w23[-1]*2^3)";
        let e1 = parse_expr(e1_str).unwrap();
        let e2_str = format!("{}", e1);
        assert_eq!(e1_str, e2_str);
    }
}
