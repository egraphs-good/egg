use lalrpop_util::lalrpop_mod;

use crate::expr::SimpleExpr;

lalrpop_mod!(pub grammar, "/parse/grammar.rs");

pub fn parse(s: &str) -> SimpleExpr {
    let mut expr = SimpleExpr::default();
    let parser = grammar::TermParser::new();
    let _root_id = parser.parse(&mut expr, s).unwrap();
    expr
}

#[cfg(test)]
mod tests {

    use super::*;

    use crate::expr::{op, var};

    #[test]
    fn simple_parse() {
        let mut expr = SimpleExpr::default();

        // SimpleExpr doesn't do hashcons
        let a = expr.add(var(1));
        let b = expr.add(var(1));

        expr.add(op(32, vec![a, b]));

        let expr2 = parse("(o32 v1 v1)");

        assert_eq!(expr, expr2);
    }
}
