pub mod simple {
    use egg::*;

    define_language! {
        pub enum SimpleLanguage {
            Num(i32),
            "+" = Add([Id; 2]),
            "*" = Mul([Id; 2]),
            Symbol(Symbol),
        }
    }

    pub fn make_rules() -> Vec<Rewrite<SimpleLanguage, ()>> {
        vec![
            rewrite!("commute-add"; "(+ ?a ?b)" => "(+ ?b ?a)"),
            rewrite!("commute-mul"; "(* ?a ?b)" => "(* ?b ?a)"),
            rewrite!("add-0"; "(+ ?a 0)" => "?a"),
            rewrite!("mul-0"; "(* ?a 0)" => "0"),
            rewrite!("mul-1"; "(* ?a 1)" => "?a"),
        ]
    }
}
