use std::collections::HashMap;
use lalrpop_util::lalrpop_mod;

use crate::{EGraph};

lalrpop_mod!(pub grammar, "/parse/grammar.rs");

fn parse(s: &str) -> EGraph {
    let mut egraph = EGraph::default();
    let parser = grammar::TermParser::new();
    let _root_id = parser.parse(&mut egraph, s).unwrap();
    egraph
}

#[cfg(test)]
mod tests {

    use super::*;

    use crate::ENode;

    #[test]
    fn simple_parse() {
        let mut egraph1 = EGraph::default();

        let x = egraph1.add(ENode::Var("x".into()));
        let plus = egraph1.add(ENode::Plus(x, x));

        let egraph2 = parse("(+ x x)");

        assert_eq!(egraph1, egraph2);
    }
}
