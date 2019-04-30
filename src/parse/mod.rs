use lalrpop_util::lalrpop_mod;

use crate::expr::{tests::TestNode, Expr};

lalrpop_mod!(pub grammar, "/parse/grammar.rs");

pub fn parse(s: &str) -> Expr<TestNode> {
    let mut expr = Expr::default();
    let parser = grammar::TermParser::new();
    let _root_id = parser.parse(&mut expr, s).unwrap();
    expr
}

mod tests {

    use super::*;

    use crate::expr::tests::{op, var};

    #[test]
    fn simple_parse() {
        let mut expr = Expr::default();

        // SimpleExpr doesn't do hashcons
        let a = expr.add(var("x"));
        let b = expr.add(var("x"));

        expr.add(op("+", vec![a, b]));

        let expr2 = parse("(+ x x)");

        assert_eq!(expr, expr2);
    }
}
