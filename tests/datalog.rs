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
    fn check_not(&mut self, s: &str);
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

    fn check_not(&mut self, s: &str) {
        let true_id = self.add(Lang::True);
        for e in s.split(',') {
            let exp = e.trim().parse().unwrap();
            let id = self.add_expr(&exp);
            assert!(true_id != id, "{} is not true", e);
        }
    }
}

#[test]
fn path() {
    let mut egraph = EGraph::<Lang, ()>::default();
    egraph.assert("(edge 1 2), (edge 2 3), (edge 3 4)");
    let rules = vec![
        rewrite!("base-case"; "?x = true = (edge ?a ?b)" |- "?x = (path ?a ?b)"),
        rewrite!("transitive"; "?x = true = (path ?a ?b) = (edge ?b ?c)" |- "?x = (path ?a ?c)"),
    ];

    let mut runner = Runner::default().with_egraph(egraph).run(&rules);
    runner.egraph.check("(path 1 4)");
    runner.egraph.check_not("(path 4 1)");
}

#[test]
fn path2() {
    // `pred` function symbol allows us to insert without truth.
    let mut egraph = EGraph::<Lang, ()>::default();
    egraph.assert("(edge 1 2), (edge 2 3), (edge 3 4), (edge 1 4)");
    let rules = vec![
        rewrite!("base-case"; "?x = (edge ?a ?b), ?t = true" |- "?t = (pred (path ?a ?b))"),
        rewrite!("transitive"; "?x = (path ?a ?b), ?y = (edge ?b ?c), ?t = true" |- "?t = (pred (path ?a ?c))"),
    ];
    let mut runner = Runner::default().with_egraph(egraph).run(&rules);
    runner.egraph.check("(pred (path 1 4))");
    runner.egraph.check("(pred (path 2 3))");
    runner.egraph.check_not("(pred (path 4 1))");
    runner.egraph.check_not("(pred (path 3 1))");
}

#[test]
fn ctx_transfer() {
    let mut egraph = EGraph::<Lang, ()>::default();
    egraph.assert("(lte ctx1 ctx2)");
    egraph.assert("(lte ctx2 ctx2)");
    egraph.assert("(lte ctx1 ctx1)");
    let x2 = egraph.add_expr(&"(tag x ctx2)".parse().unwrap());
    let y2 = egraph.add_expr(&"(tag y ctx2)".parse().unwrap());
    let z2 = egraph.add_expr(&"(tag z ctx2)".parse().unwrap());

    let x1 = egraph.add_expr(&"(tag x ctx1)".parse().unwrap());
    let y1 = egraph.add_expr(&"(tag y ctx1)".parse().unwrap());
    let z1 = egraph.add_expr(&"(tag z ctx2)".parse().unwrap());
    egraph.union(x1, y1);
    egraph.union(y2, z2);
    let rules = vec![
        rewrite!("context-transfer"; "?x = (tag ?a ?ctx1) = (tag ?b ?ctx1), ?t = true = (lte ?ctx1 ?ctx2), ?a1 = (tag ?a ?ctx2), ?b1 = (tag ?b ?ctx2)" |- "?a1 = ?b1"),
    ];
    let runner = Runner::default().with_egraph(egraph).run(&rules);
    assert_eq!(runner.egraph.find(x1), runner.egraph.find(y1));
    assert_eq!(runner.egraph.find(y2), runner.egraph.find(z2));

    assert_eq!(runner.egraph.find(x2), runner.egraph.find(y2));
    assert_eq!(runner.egraph.find(x2), runner.egraph.find(z2));

    assert!(runner.egraph.find(y1) != runner.egraph.find(z1));
    assert!(runner.egraph.find(x1) != runner.egraph.find(z1));
}
