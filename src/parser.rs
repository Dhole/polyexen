use crate::expr::Expr;

use num_bigint::BigUint;

pub type Ex = Expr<String>;

extern crate pest;

use pest::{error::Error, Parser};

#[derive(Parser)]
#[grammar = "grammar.pest"]
struct ExprParser;
use pest::iterators::Pairs;
use pest::pratt_parser::PrattParser;

lazy_static! {
    static ref PRATT_PARSER: PrattParser<Rule> = {
        use pest::pratt_parser::{Assoc::*, Op};
        use Rule::*;

        PrattParser::new()
            .op(Op::infix(add, Left) | Op::infix(subtract, Left))
            .op(Op::infix(multiply, Left))
    };
}

pub fn parse_pairs(expression: Pairs<Rule>) -> Ex {
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
            Rule::neg => (Neg(Box::new(parse_pairs(primary.into_inner()))), true),
            Rule::expr => (parse_pairs(primary.into_inner()), false),
            _ => unreachable!(),
        })
        // lcont and rcont tell wether the lhs and rhs terms belong to the same expr or not
        .map_infix(|(lhs, lcont), op, (rhs, rcont)| {
            (
                match op.as_rule() {
                    Rule::add => match (lhs, lcont & rcont) {
                        (Sum(mut es), true) => {
                            es.push(rhs);
                            Sum(es)
                        }
                        (lhs, _) => Sum(vec![lhs, rhs]),
                    },
                    Rule::subtract => match (lhs, lcont & rcont) {
                        (Sum(mut es), true) => {
                            es.push(Neg(Box::new(rhs)));
                            Sum(es)
                        }
                        (lhs, _) => Sum(vec![lhs, Neg(Box::new(rhs))]),
                    },
                    Rule::multiply => match (lhs, lcont & rcont) {
                        (Mul(mut es), true) => {
                            es.push(rhs);
                            Mul(es)
                        }
                        (lhs, _) => Mul(vec![lhs, rhs]),
                    },
                    _ => unreachable!(),
                },
                true,
            )
        })
        .parse(expression)
        .0
}

pub fn parse(src: &str) -> Result<Ex, Error<Rule>> {
    let r = ExprParser::parse(Rule::expr, src)?;
    Ok(parse_pairs(r))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse() {
        let r = ExprParser::parse(Rule::expr, "(-1 + 2)");
        dbg!(&r);
        let e = parse_pairs(r.unwrap());
        println!("{:?}", e);
        println!("{}", e);
    }
}
