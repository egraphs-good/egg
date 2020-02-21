use std::rc::Rc;

use crate::{EGraph, Id, Language, Metadata, SearchMatches, Subst};

/// A rewrite that searches for the lefthand side and applies the righthand side.
///
/// The [`rewrite!`] is the easiest way to create rewrites.
///
/// A [`Rewrite`] consists principally of a [`Searcher`] (the lefthand
/// side) and an [`Applier`] (the righthand side).
/// It additionally stores a name used to refer to the rewrite and a
/// long name used for debugging.
///
/// [`rewrite!`]: macro.rewrite.html
/// [`Searcher`]: trait.Searcher.html
/// [`Applier`]: trait.Applier.html
/// [`Condition`]: trait.Condition.html
/// [`ConditionalApplier`]: struct.ConditionalApplier.html
/// [`Rewrite`]: struct.Rewrite.html
/// [`Pattern`]: struct.Pattern.html
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
    /// Create a new [`Rewrite`]. You typically want to use the
    /// [`rewrite!`] macro instead.
    ///
    /// [`Rewrite`]: struct.Rewrite.html
    /// [`rewrite!`]: macro.rewrite.html
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

    /// Returns the name of the rewrite.
    pub fn name(&self) -> &str {
        &self.name
    }

    /// Returns the long name of the rewrite which should only be used for
    /// debugging and displaying.
    pub fn long_name(&self) -> &str {
        &self.long_name
    }

    /// Call [`search`] on the [`Searcher`].
    ///
    /// [`Searcher`]: trait.Searcher.html
    /// [`search`]: trait.Searcher.html#method.search
    pub fn search(&self, egraph: &EGraph<L, M>) -> Vec<SearchMatches> {
        self.searcher.search(egraph)
    }

    /// Call [`apply_matches`] on the [`Applier`].
    ///
    /// [`Applier`]: trait.Applier.html
    /// [`apply_matches`]: trait.Applier.html#method.apply_matches
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

/// The lefthand side of a [`Rewrite`].
///
/// A [`Searcher`] is something that can search the egraph and find
/// matching substititions.
/// Right now the only significant [`Searcher`] is [`Pattern`].
///
/// [`Rewrite`]: struct.Rewrite.html
/// [`Searcher`]: trait.Searcher.html
/// [`Pattern`]: struct.Pattern.html
pub trait Searcher<L, M>
where
    L: Language,
    M: Metadata<L>,
{
    /// Search one eclass, returning None if no matches can be found.
    /// This should not return a SearchMatches with no substs.
    fn search_eclass(&self, egraph: &EGraph<L, M>, eclass: Id) -> Option<SearchMatches>;

    /// Search the whole [`EGraph`], returning a list of all the
    /// [`SearchMatches`] where something was found.
    /// This just calls [`search_eclass`] on each eclass.
    ///
    /// [`EGraph`]: struct.EGraph.html
    /// [`search_eclass`]: trait.Searcher.html#tymethod.search_eclass
    /// [`SearchMatches`]: struct.SearchMatches.html
    fn search(&self, egraph: &EGraph<L, M>) -> Vec<SearchMatches> {
        egraph
            .classes()
            .filter_map(|e| self.search_eclass(egraph, e.id))
            .collect()
    }
}

/// The righthand side of a [`Rewrite`].
///
/// An [`Applier`] is anything that can do something with a
/// substitition ([`Subst`]). This allows you to implement rewrites
/// that determine when and how to respond to a match using custom
/// logic, including access to the [`Metadata`] of an [`EClass`].
///
/// Notably, [`Pattern`] implements [`Applier`], which suffices in
/// most cases.
/// Additionally, `egg` provides [`ConditionalApplier`] to stack
/// [`Condition`]s onto an [`Applier`], which in many cases can save
/// you from having to implement your own applier.
///
/// # Example
/// ```
/// use egg::{rewrite as rw, *};
///
/// define_language! {
///     enum Math {
///         Num(i32),
///         Add = "+",
///         Mul = "*",
///         Symbol(String),
///     }
/// }
///
/// // Our metadata in this case will be size of the smallest
/// // represented expression in the eclass.
/// #[derive(Debug)]
/// struct Meta {
///     size: usize,
/// }
///
/// type EGraph = egg::EGraph<Math, Meta>;
///
/// impl Metadata<Math> for Meta {
///     type Error = ();
///     fn merge(&self, other: &Self) -> Self {
///         let size = self.size.min(other.size);
///         Meta { size }
///     }
///     fn make(enode: ENode<Math, &Self>) -> Self {
///         let size = AstSize.cost(&enode.map_children(|c| c.size));
///         Meta { size }
///     }
/// }
///
/// let rules = &[
///     rw!("commute-add"; "(+ ?a ?b)" => "(+ ?b ?a)"),
///     rw!("commute-mul"; "(* ?a ?b)" => "(* ?b ?a)"),
///     rw!("add-0"; "(+ ?a 0)" => "?a"),
///     rw!("mul-0"; "(* ?a 0)" => "0"),
///     rw!("mul-1"; "(* ?a 1)" => "?a"),
///     // the rewrite macro parses the rhs as a single token tree, so
///     // we wrap it in braces (parens work too).
///     rw!("funky"; "(+ ?a (* ?b ?c))" => { Funky {
///         a: "?a".parse().unwrap(),
///         b: "?b".parse().unwrap(),
///         c: "?c".parse().unwrap(),
///     }}),
/// ];
///
/// struct Funky {
///     a: Var,
///     b: Var,
///     c: Var,
/// }
/// impl Applier<Math, Meta> for Funky {
///     fn apply_one(&self, egraph: &mut EGraph, matched_id: Id, subst: &Subst) -> Vec<Id> {
///         let a: Id = subst[&self.a];
///         // In a custom Applier, you can inspect the Metadata,
///         // which is powerful combination!
///         let meta_for_a: &Meta = &egraph[a].metadata;
///         if meta_for_a.size > 50 {
///             println!("Too big! Not doing anything");
///             vec![]
///         } else {
///             // we're going to manually add:
///             // (+ (+ ?a 0) (* (+ ?b 0) (+ ?c 0)))
///             // to be unified with the original:
///             // (+    ?a    (*    ?b       ?c   ))
///             let b: Id = subst[&self.b];
///             let c: Id = subst[&self.c];
///             let zero = egraph.add(enode!(Math::Num(0)));
///             let a0 = egraph.add(enode!(Math::Add, a, zero));
///             let b0 = egraph.add(enode!(Math::Add, b, zero));
///             let c0 = egraph.add(enode!(Math::Add, c, zero));
///             let b0c0 = egraph.add(enode!(Math::Mul, b0, c0));
///             let a0b0c0 = egraph.add(enode!(Math::Add, a0, b0c0));
///             // NOTE: we just return the id according to what we
///             // want unified with matched_id. The `apply_matches`
///             // method actually does the union, _not_ `apply_one`.
///             vec![a0b0c0]
///         }
///     }
/// }
///
/// let start = "(+ x (* y z))".parse().unwrap();
/// SimpleRunner::default().run_expr(start, rules);
/// ```
/// [`Pattern`]: struct.Pattern.html
/// [`EClass`]: struct.EClass.html
/// [`Rewrite`]: struct.Rewrite.html
/// [`ConditionalApplier`]: struct.ConditionalApplier.html
/// [`Subst`]: struct.Subst.html
/// [`Applier`]: trait.Applier.html
/// [`Condition`]: trait.Condition.html
/// [`Metadata`]: trait.Metadata.html
pub trait Applier<L, M>
where
    L: Language,
    M: Metadata<L>,
{
    /// Apply many substititions.
    ///
    /// This method should call [`apply_one`] for each match and then
    /// unify the results with the matched eclass.
    /// This should return a list of [`Id`]s where the union actually
    /// did something.
    ///
    /// The default implementation does this and should suffice for
    /// most use cases.
    ///
    /// [`Id`]: type.Id.html
    /// [`apply_one`]: trait.Applier.html#method.apply_one
    fn apply_matches(&self, egraph: &mut EGraph<L, M>, matches: &[SearchMatches]) -> Vec<Id> {
        let mut added = vec![];
        for mat in matches {
            for subst in &mat.substs {
                let ids = self
                    .apply_one(egraph, mat.eclass, subst)
                    .into_iter()
                    .filter_map(|id| egraph.union_if_different(id, mat.eclass));
                added.extend(ids)
            }
        }
        added
    }

    /// Apply a single substitition.
    ///
    /// An [`Applier`] should only add things to the egraph here,
    /// _not_ union them with the id `eclass`.
    /// That is the responsibility of the [`apply_matches`] method.
    /// The `eclass` parameter allows the implementer to inspect the
    /// eclass where the match was found if they need to.
    ///
    /// This should return a list of [`Id`]s of things you'd like to
    /// be unioned with `eclass`. There can be zero, one, or many.
    ///
    /// [`Applier`]: trait.Applier.html
    /// [`Id`]: type.Id.html
    /// [`apply_matches`]: trait.Applier.html#method.apply_matches
    fn apply_one(&self, egraph: &mut EGraph<L, M>, eclass: Id, subst: &Subst) -> Vec<Id>;
}

/// An [`Applier`] that checks a [`Condition`] before applying.
///
/// A [`ConditionalApplier`] simply calls [`check`] on the
/// [`Condition`] before calling [`apply_one`] on the inner
/// [`Applier`].
///
/// See the [`rewrite!`] macro documentation for an example.
///
/// [`rewrite!`]: macro.rewrite.html
/// [`Applier`]: trait.Applier.html
/// [`apply_one`]: trait.Applier.html#method.apply_one
/// [`Condition`]: trait.Condition.html
/// [`check`]: trait.Condition.html#method.check
/// [`ConditionalApplier`]: struct.ConditionalApplier.html
#[derive(Clone, Debug)]
pub struct ConditionalApplier<C, A> {
    /// The [`Condition`] to [`check`] before calling [`apply_one`] on
    /// `applier`.
    ///
    /// [`apply_one`]: trait.Applier.html#method.apply_one
    /// [`Condition`]: trait.Condition.html
    /// [`check`]: trait.Condition.html#method.check
    pub condition: C,
    /// The inner [`Applier`] to call once `condition` passes.
    ///
    /// [`Applier`]: trait.Applier.html
    pub applier: A,
}

impl<C, A, L, M> Applier<L, M> for ConditionalApplier<C, A>
where
    L: Language,
    M: Metadata<L>,
    A: Applier<L, M>,
    C: Condition<L, M>,
{
    fn apply_one(&self, egraph: &mut EGraph<L, M>, eclass: Id, subst: &Subst) -> Vec<Id> {
        if self.condition.check(egraph, eclass, subst) {
            self.applier.apply_one(egraph, eclass, subst)
        } else {
            vec![]
        }
    }
}

/// A condition to check in a [`ConditionalApplier`].
///
/// See the [`ConditionalApplier`] docs.
///
/// Notably, any function ([`Fn`]) that doesn't mutate other state
/// and matches the signature of [`check`] implements [`Condition`].
///
/// [`check`]: trait.Condition.html#method.check
/// [`Fn`]: https://doc.rust-lang.org/std/ops/trait.Fn.html
/// [`ConditionalApplier`]: struct.ConditionalApplier.html
/// [`Condition`]: trait.Condition.html
pub trait Condition<L, M>
where
    L: Language,
    M: Metadata<L>,
{
    /// Check a condition.
    ///
    /// `eclass` is the eclass [`Id`] where the match (`subst`) occured.
    /// If this is true, then the [`ConditionalApplier`] will fire.
    ///
    /// [`Id`]: type.Id.html
    /// [`ConditionalApplier`]: struct.ConditionalApplier.html
    fn check(&self, egraph: &mut EGraph<L, M>, eclass: Id, subst: &Subst) -> bool;
}

impl<L, M, F> Condition<L, M> for F
where
    L: Language,
    M: Metadata<L>,
    F: Fn(&mut EGraph<L, M>, Id, &Subst) -> bool,
{
    fn check(&self, egraph: &mut EGraph<L, M>, eclass: Id, subst: &Subst) -> bool {
        self(egraph, eclass, subst)
    }
}

/// A [`Condition`] that checks if two terms are equivalent.
///
/// This condition adds its two [`Applier`]s to the egraph and passes
/// if and only if they are equivalent (in the same eclass).
///
/// [`Applier`]: trait.Applier.html
/// [`Condition`]: trait.Condition.html
pub struct ConditionEqual<A1, A2>(pub A1, pub A2);

impl<L, M, A1, A2> Condition<L, M> for ConditionEqual<A1, A2>
where
    L: Language,
    M: Metadata<L>,
    A1: Applier<L, M>,
    A2: Applier<L, M>,
{
    fn check(&self, egraph: &mut EGraph<L, M>, eclass: Id, subst: &Subst) -> bool {
        let a1 = self.0.apply_one(egraph, eclass, subst);
        let a2 = self.1.apply_one(egraph, eclass, subst);
        assert_eq!(a1.len(), 1);
        assert_eq!(a2.len(), 1);
        a1[0] == a2[0]
    }
}

#[cfg(test)]
mod tests {

    use crate::{enode as e, *};

    #[test]
    fn conditional_rewrite() {
        crate::init_logger();
        let mut egraph = EGraph::<String, ()>::default();

        let x = egraph.add(e!("x"));
        let y = egraph.add(e!("2"));
        let mul = egraph.add(e!("*", x, y));

        let true_pat: Pattern<String> = "TRUE".parse().unwrap();
        let true_id = egraph.add(e!("TRUE"));

        let pow2b: Pattern<String> = "(is-power2 ?b)".parse().unwrap();
        let mul_to_shift = rewrite!(
            "mul_to_shift";
            "(* ?a ?b)" => "(>> ?a (log2 ?b))"
            if ConditionEqual(pow2b, true_pat)
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
                subst: &Subst,
            ) -> Vec<Id> {
                let a: Var = "?a".parse().unwrap();
                let b: Var = "?b".parse().unwrap();
                let a = get(&egraph, subst[&a]);
                let b = get(&egraph, subst[&b]);
                let s = format!("{}{}", a, b);
                vec![egraph.add(e!(&s))]
            }
        }

        let fold_add = rewrite!(
            "fold_add"; "(+ ?a ?b)" => { Appender }
        );

        fold_add.run(&mut egraph);
        assert_eq!(egraph.equivs(&start, &goal), vec![egraph.find(root)]);
    }
}
