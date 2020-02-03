use std::rc::Rc;

use crate::{EGraph, Id, Language, Metadata, SearchMatches, WildMap};

// TODO display
#[derive(Clone)]
#[non_exhaustive]
pub struct Rewrite<L, M> {
    name: String,
    long_name: String,
    searcher: Rc<dyn Searcher<L, M>>,
    applier: Rc<dyn Applier<L, M>>,
}

impl<L: Language, M: Metadata<L>> Rewrite<L, M> {
    pub fn new(
        name: impl Into<String>,
        long_name: impl Into<String>,
        searcher: impl Searcher<L, M> + 'static,
        applier: impl Applier<L, M> + 'static,
    ) -> Self {
        Self {
            name: name.into(),
            long_name: long_name.into(),
            searcher: Rc::new(searcher),
            applier: Rc::new(applier),
        }
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn long_name(&self) -> &str {
        &self.long_name
    }

    pub fn search(&self, egraph: &EGraph<L, M>) -> Vec<SearchMatches> {
        self.searcher.search(egraph)
    }

    pub fn apply(&self, egraph: &mut EGraph<L, M>, matches: &[SearchMatches]) -> Vec<Id> {
        self.applier.apply_matches(egraph, matches)
    }

    /// This `run` is for testing use only. You should use things
    /// from the `egg::run` module
    #[cfg(test)]
    pub(crate) fn run(&self, egraph: &mut EGraph<L, M>) -> Vec<Id> {
        let start = instant::Instant::now();

        let matches = self.search(egraph);
        log::debug!("Found rewrite {} {} times", self.name, matches.len());

        let ids = self.apply(egraph, &matches);
        let elapsed = start.elapsed();
        log::debug!(
            "Applied rewrite {} {} times in {}.{:03}",
            self.name,
            ids.len(),
            elapsed.as_secs(),
            elapsed.subsec_millis()
        );

        ids
    }
}

pub trait Searcher<L, M>
where
    L: Language,
    M: Metadata<L>,
{
    fn search_eclass(&self, egraph: &EGraph<L, M>, eclass: Id) -> Option<SearchMatches>;
    fn search(&self, egraph: &EGraph<L, M>) -> Vec<SearchMatches> {
        egraph
            .classes()
            .filter_map(|e| self.search_eclass(egraph, e.id))
            .collect()
    }
}

pub trait Applier<L, M>
where
    L: Language,
    M: Metadata<L>,
{
    fn apply_matches(&self, egraph: &mut EGraph<L, M>, matches: &[SearchMatches]) -> Vec<Id> {
        let mut added = vec![];
        for mat in matches {
            for mapping in &mat.mappings {
                let ids = self
                    .apply_one(egraph, mat.eclass, mapping)
                    .into_iter()
                    .filter_map(|id| egraph.union_if_different(id, mat.eclass));
                added.extend(ids)
            }
        }
        added
    }
    fn apply_one(&self, egraph: &mut EGraph<L, M>, eclass: Id, mapping: &WildMap) -> Vec<Id>;
}

#[derive(Clone, Debug)]
pub struct ConditionalApplier<C, A> {
    pub condition: C,
    pub applier: A,
}

impl<C, A, L, M> Applier<L, M> for ConditionalApplier<C, A>
where
    L: Language,
    M: Metadata<L>,
    A: Applier<L, M>,
    C: Condition<L, M>,
{
    fn apply_one(&self, egraph: &mut EGraph<L, M>, eclass: Id, mapping: &WildMap) -> Vec<Id> {
        if self.condition.check(egraph, eclass, mapping) {
            self.applier.apply_one(egraph, eclass, mapping)
        } else {
            vec![]
        }
    }
}

pub trait Condition<L, M>
where
    L: Language,
    M: Metadata<L>,
{
    fn check(&self, egraph: &mut EGraph<L, M>, eclass: Id, mapping: &WildMap) -> bool;
}

impl<L, M, F> Condition<L, M> for F
where
    L: Language,
    M: Metadata<L>,
    F: Fn(&mut EGraph<L, M>, Id, &WildMap) -> bool,
{
    fn check(&self, egraph: &mut EGraph<L, M>, eclass: Id, mapping: &WildMap) -> bool {
        self(egraph, eclass, mapping)
    }
}

pub struct ConditionEqual<A1, A2>(pub A1, pub A2);
impl<L, M, A1, A2> Condition<L, M> for ConditionEqual<A1, A2>
where
    L: Language,
    M: Metadata<L>,
    A1: Applier<L, M>,
    A2: Applier<L, M>,
{
    fn check(&self, egraph: &mut EGraph<L, M>, eclass: Id, mapping: &WildMap) -> bool {
        let a1 = self.0.apply_one(egraph, eclass, mapping);
        let a2 = self.1.apply_one(egraph, eclass, mapping);
        assert_eq!(a1.len(), 1);
        assert_eq!(a2.len(), 1);
        a1[0] == a2[0]
    }
}

#[cfg(test)]
mod tests {

    use crate::{enode as e, *};

    fn wc<L: Language>(name: &QuestionMarkName) -> Pattern<L> {
        Pattern::Wildcard(name.clone(), crate::pattern::WildcardKind::Single)
    }

    #[test]
    fn conditional_rewrite() {
        crate::init_logger();
        let mut egraph = EGraph::<String, ()>::default();

        let pat = |e| Pattern::ENode(Box::new(e));
        let x = egraph.add(e!("x"));
        let y = egraph.add(e!("2"));
        let mul = egraph.add(e!("*", x, y));

        let true_pat = pat(e!("TRUE"));
        let true_id = egraph.add(e!("TRUE"));

        let a: QuestionMarkName = "?a".parse().unwrap();
        let b: QuestionMarkName = "?b".parse().unwrap();

        let mul_to_shift = rewrite!(
            "mul_to_shift";
            { pat(e!("*", wc(&a), wc(&b))) } =>
            { pat(e!(">>", wc(&a), pat(e!("log2", wc(&b))),)) }
            if ConditionEqual(
                pat(e!("is-power2", wc(&b))),
                true_pat,
            )
        );

        println!("rewrite shouldn't do anything yet");
        egraph.rebuild();
        let apps = mul_to_shift.run(&mut egraph);
        assert_eq!(apps, vec![]);

        println!("Add the needed equality");
        let two_ispow2 = egraph.add(e!("is-power2", y));
        egraph.union(two_ispow2, true_id);

        println!("Should fire now");
        egraph.rebuild();
        let apps = mul_to_shift.run(&mut egraph);
        assert_eq!(apps, vec![egraph.find(mul)]);
    }

    #[test]
    fn fn_rewrite() {
        crate::init_logger();
        let mut egraph = EGraph::<String, ()>::default();

        let start = "(+ x y)".parse().unwrap();
        let goal = "xy".parse().unwrap();

        let root = egraph.add_expr(&start);

        let a: QuestionMarkName = "?a".parse().unwrap();
        let b: QuestionMarkName = "?b".parse().unwrap();

        fn get(egraph: &EGraph<String, ()>, id: Id) -> &str {
            &egraph[id].nodes[0].op
        }

        #[derive(Debug)]
        struct Appender;
        impl Applier<String, ()> for Appender {
            fn apply_one(
                &self,
                egraph: &mut EGraph<String, ()>,
                _eclass: Id,
                map: &WildMap,
            ) -> Vec<Id> {
                let a: QuestionMarkName = "?a".parse().unwrap();
                let b: QuestionMarkName = "?b".parse().unwrap();
                let a = get(&egraph, map[&a][0]);
                let b = get(&egraph, map[&b][0]);
                let s = format!("{}{}", a, b);
                vec![egraph.add(e!(&s))]
            }
        }

        let pat = |e| Pattern::ENode(Box::new(e));
        let fold_add = rewrite!(
            "fold_add";
            { pat(e!("+", wc(&a), wc(&b))) } =>
            { Appender }
        );

        fold_add.run(&mut egraph);
        assert_eq!(egraph.equivs(&start, &goal), vec![egraph.find(root)]);
    }
}
