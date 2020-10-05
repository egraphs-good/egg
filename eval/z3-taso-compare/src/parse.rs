use crate::model::*;
use egg::*;
use pest::{iterators::Pair, Parser};

#[derive(pest_derive::Parser)]
#[grammar = "equation.pest"]
pub struct EqParser;

pub fn parse_exp(e: Pair<Rule>) -> String {
    match e.as_rule() {
        Rule::name => e.as_str().to_owned(),
        Rule::expr => parse_exp(e.into_inner().next().unwrap()),
        Rule::apply => {
            let mut inner_rules = e.into_inner();
            let op = parse_exp(inner_rules.next().unwrap());
            let args = parse_exp(inner_rules.next().unwrap());
            format!("({} {})", op, args)
        }
        Rule::args => {
            let arg_ss: Vec<_> = e.into_inner().map(parse_exp).collect();
            arg_ss.join(" ")
        }
        _ => unreachable!(),
    }
}

pub fn parse_eq(e: Pair<Rule>) -> (RecExpr<Mdl>, RecExpr<Mdl>) {
    match e.as_rule() {
        Rule::eq => {
            let mut inner_rules = e.into_inner();
            let lhs = parse_exp(inner_rules.next().unwrap());
            let rhs = parse_exp(inner_rules.next().unwrap());
            // println!("(not (= {} {}))", lhs, rhs);
            (lhs.parse().unwrap(), rhs.parse().unwrap())
        }
        _ => unreachable!(),
    }
}

pub fn parse_rules(rs_s: &str) -> Vec<(RecExpr<Mdl>, RecExpr<Mdl>)> {
    let rs = EqParser::parse(Rule::prog, rs_s)
        .expect("parse error")
        .next()
        .unwrap();
    match rs.as_rule() {
        Rule::prog => rs.into_inner().map(parse_eq).collect(),
        _ => unreachable!(),
    }
}
