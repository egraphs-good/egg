use egg::*;

define_language! {
    enum Lang {
        "true" = True,
        Int(i32),
        Relation(Symbol, Box<[Id]>),
    }
}

trait DatalogExtTrait {
    fn assert(&mut self, s: &str);
    fn check(&mut self, s: &str);
}

impl DatalogExtTrait for EGraph<Lang, ()> {
    fn assert(&mut self, s: &str) {
        let true_id = self.add(Lang::True);
        for e in s.split(',') {
            let exp = e.trim().parse().unwrap();
            let id = self.add_expr(&exp);
            self.union(true_id, id);
        }
    }

    fn check(&mut self, s: &str) {
        let true_id = self.add(Lang::True);
        for e in s.split(',') {
            let exp = e.trim().parse().unwrap();
            let id = self.add_expr(&exp);
            assert_eq!(true_id, id, "{} is not true", e);
        }
    }
}

#[test]
fn path() {
    let mut egraph = EGraph::<Lang, ()>::default();
    egraph.assert("(edge 1 2), (edge 2 3), (edge 3 4)");
    let rules = vec![
        rewrite!("base-case"; "?x = true = (edge ?a ?b)" ==> "?x = (path ?a ?b)"),
        rewrite!("transitive"; "?x = true = (path ?a ?b) = (edge ?b ?c)" ==> "?x = (path ?a ?c)"),
    ];

    let mut runner = Runner::default().with_egraph(egraph).run(&rules);
    runner.egraph.check("(path 1 4)");
}
