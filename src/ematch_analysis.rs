use crate::legacy::{concat_vecs, HashMap, HashSet};
use crate::{
    Analysis, AnalysisData, AstSize, EClass, EGraph, EGraphT, Extractor, Id, Justification,
    Language, Pattern, RecExpr, Rewrite, Searcher,
};
use log::trace;
use std::fmt::Display;
use std::mem;

/// An [`EGraph`] that includes an [`EMatchingAnalysis`]
pub type EMGraph<L, N> = EGraph<L, (N, EMatchingAnalysis<L>)>;

/// An [`EClass`] that includes an [`EMatchingAnalysis`]
pub type EMClass<L, D> = EClass<(D, EMatchingData<L>)>;

/// An [`Analysis`] that supports backtracking e-matching
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde-1", derive(serde::Serialize, serde::Deserialize))]
pub struct EMatchingAnalysis<L: Language> {
    #[cfg_attr(feature = "serde-1", serde(skip))]
    #[cfg_attr(feature = "serde-1", serde(default = "default_classes_by_op"))]
    pub(crate) classes_by_op: HashMap<L::Discriminant, HashSet<Id>>,
}

#[cfg(feature = "serde-1")]
fn default_classes_by_op<K>() -> HashMap<K, HashSet<Id>> {
    HashMap::default()
}

pub type EMatchingData<L> = Vec<L>;

impl<L: Language> Default for EMatchingAnalysis<L> {
    fn default() -> Self {
        EMatchingAnalysis {
            classes_by_op: Default::default(),
        }
    }
}

impl<L: Language> AnalysisData<L> for EMatchingAnalysis<L> {
    type Data = EMatchingData<L>; // EClass.nodes
}

impl<L: Language> Analysis<L> for EMatchingAnalysis<L> {
    fn make<E: EGraphT<L, N = Self>>(_: E, enode: &L) -> Self::Data {
        vec![enode.clone()]
    }

    fn merge<E: EGraphT<L, N = Self>>(
        mut egraph: E,
        new_root: Id,
        _: Id,
        other_data: Self::Data,
        _: &[Id],
        _: &Option<Justification>,
    ) {
        concat_vecs(egraph.data_mut(new_root), other_data)
    }

    fn rebuild<E: EGraphT<L, N = Self>>(mut egraph: E, will_repeat: bool) -> bool {
        if will_repeat {
            return false;
        }
        let mut classes_by_op = mem::take(&mut egraph.analysis_mut().classes_by_op);
        classes_by_op.values_mut().for_each(|ids| ids.clear());
        let egraph = egraph.deref_mut();

        let mut trimmed = 0;
        let uf = &mut egraph.unionfind;

        for class in egraph.classes.values_mut() {
            let id = class.id;
            let data = E::proj_data_mut(&mut class.data);
            let old_len = data.len();
            data.iter_mut()
                .for_each(|n| n.update_children(|id| uf.find_mut(id)));
            data.sort_unstable();
            data.dedup();

            trimmed += old_len - data.len();

            let mut add = |n: &L| {
                classes_by_op
                    .entry(n.discriminant())
                    .or_default()
                    .insert(id)
            };

            // we can go through the ops in order to dedup them, becaue we
            // just sorted them
            let mut nodes = data.iter();
            if let Some(mut prev) = nodes.next() {
                add(prev);
                for n in nodes {
                    if !prev.matches(n) {
                        add(n);
                        prev = n;
                    }
                }
            }
        }

        #[cfg(debug_assertions)]
        for ids in classes_by_op.values_mut() {
            let unique: HashSet<Id> = ids.iter().copied().collect();
            assert_eq!(ids.len(), unique.len());
        }

        E::proj_mut(&mut egraph.analysis).classes_by_op = classes_by_op;
        log::info!("trimmed nodes: {trimmed}");
        false
    }
}

impl<L: Language, N: Analysis<L>> EMGraph<L, N> {
    pub(crate) fn check_each_explain(&mut self, rules: &[&Rewrite<L, N>]) -> bool {
        if let Some(explain) = &mut self.explain {
            explain.with_nodes(&self.nodes).check_each_explain(rules)
        } else {
            panic!("Can't check explain when explanations are off");
        }
    }

    /// Checks whether two [`RecExpr`]s are equivalent.
    /// Returns a list of id where both expression are represented.
    /// In most cases, there will none or exactly one id.
    ///
    pub fn equivs(&self, expr1: &RecExpr<L>, expr2: &RecExpr<L>) -> Vec<Id> {
        let pat1 = Pattern::from(expr1.as_ref());
        let pat2 = Pattern::from(expr2.as_ref());
        let matches1 = pat1.search(self);
        trace!("Matches1: {:?}", matches1);

        let matches2 = pat2.search(self);
        trace!("Matches2: {:?}", matches2);

        let mut equiv_eclasses = Vec::new();

        for m1 in &matches1 {
            for m2 in &matches2 {
                if self.find(m1.eclass) == self.find(m2.eclass) {
                    equiv_eclasses.push(m1.eclass)
                }
            }
        }

        equiv_eclasses
    }

    /// Panic if the given eclass doesn't contain the given patterns
    ///
    /// Useful for testing.
    pub fn check_goals(&self, id: Id, goals: &[Pattern<L>])
    where
        L: Display,
    {
        let (cost, best) = Extractor::new(self, AstSize).find_best(id);
        println!("End ({}): {}", cost, best.pretty(80));

        for (i, goal) in goals.iter().enumerate() {
            println!("Trying to prove goal {}: {}", i, goal.pretty(40));
            let matches = goal.search_eclass(self, id);
            if matches.is_none() {
                let best = Extractor::new(self, AstSize).find_best(id).1;
                panic!(
                    "Could not prove goal {}:\n\
                     {}\n\
                     Best thing found:\n\
                     {}",
                    i,
                    goal.pretty(40),
                    best.pretty(40),
                );
            }
        }
    }
}
