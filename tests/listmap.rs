use std::sync::Arc;

use egg::*;

define_language! {
    enum MyLang {
        Num(i32),
        "f" = F([Id; 2]),
        "g" = G(Id), // G is variadic, modeled as taking a single list
        "list" = List(Vec<Id>),
        Symbol(Symbol),
        "op" = Op(Id),
    }
}

struct ListMapApplier {
    new_list_var: Var,
    list_pattern: PatternAst<MyLang>,
    elem_pattern: PatternAst<MyLang>,
}

impl ListMapApplier {
    pub fn new(list_pattern: &str, elem_pattern: &str) -> Self {
        Self {
            new_list_var: "?list2".parse().unwrap(),
            list_pattern: list_pattern.parse().unwrap(),
            elem_pattern: elem_pattern.parse().unwrap(),
        }
    }
}

impl Applier<MyLang, ()> for ListMapApplier {
    fn apply_one(
        &self,
        egraph: &mut EGraph<MyLang, ()>,
        eclass: Id,
        subst: &Subst,
        _searcher_ast: Option<&PatternAst<MyLang>>,
        _rule_name: Symbol,
    ) -> Vec<Id> {
        let mut subst = subst.clone();

        let data = subst
            .data
            .as_ref()
            .expect("no data, did you use ListMapSearcher?");
        let list_matches = data
            .downcast_ref::<ListMatches>()
            .expect("wrong data type")
            .clone();

        let new_list = list_matches
            .iter()
            .map(|list_subst| {
                let mut subst = subst.clone();
                subst.extend(list_subst.iter());
                egraph.add_instantiation(&self.elem_pattern, &subst)
            })
            .collect();

        subst.insert(self.new_list_var, egraph.add(MyLang::List(new_list)));
        let result_id = egraph.add_instantiation(&self.list_pattern, &subst);

        if egraph.union(eclass, result_id) {
            vec![result_id]
        } else {
            vec![]
        }
    }

    fn vars(&self) -> Vec<Var> {
        let mut vars = self.list_pattern.vars();
        vars.extend(self.elem_pattern.vars());
        vars.retain(|v| *v != self.new_list_var); // this is bound by the applier itself
        vars
    }
}

struct ListMapSearcher {
    list_pattern: Pattern<MyLang>,
    list_var: Var,
    top_level_elem_vars: Vec<Var>,
    elem_pattern: Pattern<MyLang>,
}

impl ListMapSearcher {
    fn new(list_pattern: &str, elem_pattern: &str) -> Self {
        Self {
            list_var: "?list".parse().unwrap(),
            list_pattern: list_pattern.parse().unwrap(),
            elem_pattern: elem_pattern.parse().unwrap(),
            top_level_elem_vars: ["?TOP-a", "?TOP-b"]
                .iter()
                .map(|s| s.parse().unwrap())
                .collect(),
        }
    }
}

type ListMatches = Vec<Subst>;

impl Searcher<MyLang, ()> for ListMapSearcher {
    fn search_eclass_with_limit(
        &self,
        egraph: &EGraph<MyLang, ()>,
        eclass: Id,
        limit: usize,
    ) -> Option<SearchMatches<MyLang>> {
        let mut matches = self
            .list_pattern
            .search_eclass_with_limit(egraph, eclass, limit)?;
        for subst in &mut matches.substs {
            let list_id = subst[self.list_var];
            let list_children: &[Id] = egraph[list_id]
                .iter()
                .find(|n| matches!(n, MyLang::List(_)))
                .unwrap()
                .children();

            if list_children.is_empty() {
                panic!("List is empty")
            }

            let list_matches: Option<ListMatches> = self
                .elem_pattern
                .search_eclass_with_limit(egraph, list_children[0], limit)
                .iter()
                .flat_map(|matches0| matches0.substs.iter())
                // iterate over every subst from the matches of the first element of the list
                .find_map(|subst0| {
                    let mut substs: ListMatches = vec![subst0.clone()];
                    for &child in &list_children[1..] {
                        let child_matches = self
                            .elem_pattern
                            .search_eclass_with_limit(egraph, child, limit)?;
                        let child_subst = child_matches.substs.into_iter().find(|s| {
                            self.top_level_elem_vars
                                .iter()
                                .all(|&v| s.get(v) == subst0.get(v))
                        })?;
                        substs.push(child_subst);
                    }
                    Some(substs)
                });

            if let Some(list_matches) = list_matches {
                assert_eq!(list_matches.len(), list_children.len());
                if let Some(first) = list_matches.first() {
                    for &var in &self.top_level_elem_vars {
                        if let Some(id) = first.get(var) {
                            subst.insert(var, *id);
                        }
                    }
                }
                subst.data = Some(Arc::new(list_matches));
            }
        }

        matches.substs.retain(|s| s.data.is_some());
        if matches.substs.is_empty() {
            None
        } else {
            println!("hi");
            Some(matches)
        }
    }

    fn vars(&self) -> Vec<Var> {
        let mut vars = self.list_pattern.vars();
        vars.extend(self.elem_pattern.vars());
        vars.push(self.list_var);
        vars
    }
}

egg::test_fn! {
    pushdown,
    [
        // {} around applier needed for macro
        rewrite!("fg-pushdown"; { ListMapSearcher::new("(f ?f_arg (g ?list))", "?elem") } =>
                                { ListMapApplier::new("(g ?list2)", "(f ?f_arg ?elem)")}),
    ],
    runner = Runner::default().with_iter_limit(1),
    "(f 0 (g (list 1 2 3)))" =>
    "(g (list (f 0 1) (f 0 2) (f 0 3)))"
}

egg::test_fn! {
    pullup,
    [
        // {} around applier needed for macro
        rewrite!("fg-pullup"; { ListMapSearcher::new("(g ?list)", "(f ?TOP-a ?x)") } =>
                              { ListMapApplier::new("(f ?TOP-a (g ?list2))", "?x") }),
    ],
    // TODO how to supprt binding the same variable in each list element?
    runner = Runner::default().with_iter_limit(1),
    "(g (list (f 0 1) (f 0 2) (f 0 3)))" =>
    "(f 0 (g (list 1 2 3)))"
}

egg::test_fn! {
    #[should_panic(expected = "Could not prove goal")]
    pullup_fail,
    [
        // {} around applier needed for macro
        rewrite!("fg-pullup"; { ListMapSearcher::new("(g ?list)", "(f ?TOP-a ?x)") } =>
                              { ListMapApplier::new("(f ?TOP-a (g ?list2))", "?x") }),
    ],
    // TODO how to supprt binding the same variable in each list element?
    runner = Runner::default().with_iter_limit(1),
    "(g (list (f 0 1) (f 0 2) (f 7 3)))" =>
    "(f 0 (g (list 1 2 3)))"
}
