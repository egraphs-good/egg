use crate::generic_analysis::{Extr0, ExtrId, Extractor, Just};
use crate::legacy::UniqueQueue;
use crate::{Analysis, AnalysisData, EGraph, EGraphT, Id, Justification, Language};
use std::cmp::Ordering;
use std::fmt::{Debug, Formatter};
use std::mem;
use std::ops::BitOr;

/// Result of [`Analysis::merge`] indicating which of the inputs
/// are different from the merged result.
///
/// The fields correspond to whether the initial `a` and `b` inputs to [`Analysis::merge`]
/// were different from the final merged value.
///
/// In both cases the result may be conservative -- they may indicate `true` even
/// when there is no difference between the input and the result.
///
/// `DidMerge`s can be "or"ed together using the `|` operator.
/// This can be useful for composing analyses.
pub struct DidMerge(pub bool, pub bool);

impl BitOr for DidMerge {
    type Output = DidMerge;

    fn bitor(mut self, rhs: Self) -> Self::Output {
        self.0 |= rhs.0;
        self.1 |= rhs.1;
        self
    }
}

/** Arbitrary data associated with an [`EClass`].

`egg` allows you to associate arbitrary data with each eclass.
The [`Analysis`] allows that data to behave well even across eclasses merges.

[`Analysis`] can prove useful in many situtations.
One common one is constant folding, a kind of partial evaluation.
In that case, the metadata is basically `Option<L>`, storing
the cheapest constant expression (if any) that's equivalent to the
enodes in this eclass.
See the test files [`math.rs`] and [`prop.rs`] for more complex
examples on this usage of [`Analysis`].

If you don't care about [`Analysis`], `()` implements it trivally,
just use that.

# Example

```
use egg::legacy::{*, rewrite as rw};

define_language! {
    enum SimpleMath {
        "+" = Add([Id; 2]),
        "*" = Mul([Id; 2]),
        Num(i32),
        Symbol(Symbol),
    }
}

impl AnalysisData<SimpleMath> for ConstantFolding {
   type Data = Option<i32>;
}

// in this case, our analysis itself doesn't require any data, so we can just
// use a unit struct and derive Default
#[derive(Default)]
struct ConstantFolding;
impl Analysis<SimpleMath> for ConstantFolding {

    fn merge(&mut self, to: &mut Self::Data, from: Self::Data) -> DidMerge {
        egg::merge_max(to, from)
    }

    fn make<E: EGraphT<SimpleMath, N=Self>>(egraph: E, enode: &SimpleMath) -> Self::Data {
        let x = |i: &Id| *egraph.data(*i);
        match enode {
            SimpleMath::Num(n) => Some(*n),
            SimpleMath::Add([a, b]) => Some(x(a)? + x(b)?),
            SimpleMath::Mul([a, b]) => Some(x(a)? * x(b)?),
            _ => None,
        }
    }

    fn modify<E: EGraphT<SimpleMath, N=Self>>(mut egraph: E, id: Id) {
        if let Some(i) = *egraph.data(id) {
            let added = egraph.add(SimpleMath::Num(i));
            egraph.union(id, added);
        }
    }
}

let rules = &[
    rw!("commute-add"; "(+ ?a ?b)" => "(+ ?b ?a)"),
    rw!("commute-mul"; "(* ?a ?b)" => "(* ?b ?a)"),

    rw!("add-0"; "(+ ?a 0)" => "?a"),
    rw!("mul-0"; "(* ?a 0)" => "0"),
    rw!("mul-1"; "(* ?a 1)" => "?a"),
];

let expr = "(+ 0 (* (+ 4 -3) foo))".parse().unwrap();
let mut runner = Runner::<SimpleMath, ConstantFolding, ()>::default().with_expr(&expr).run(rules);
let just_foo = runner.egraph.add_expr(&"foo".parse().unwrap());
assert_eq!(runner.egraph.find(runner.roots[0]), runner.egraph.find(just_foo));
```

[`math.rs`]: https://github.com/egraphs-good/egg/blob/main/tests/math.rs
[`prop.rs`]: https://github.com/egraphs-good/egg/blob/main/tests/prop.rs
 */
pub trait LatticeAnalysis<L: Language>: AnalysisData<L> {
    /// Makes a new [`Analysis`] data for a given e-node.
    ///
    /// Note the mutable `egraph` parameter: this is needed for some
    /// advanced use cases, but most use cases will not need to mutate
    /// the e-graph in any way.
    /// It is **not** `make`'s responsiblity to insert the e-node;
    /// the e-node is "being inserted" when this function is called.
    /// Doing so will create an infinite loop.
    fn make<E: EGraphT<L, N = Self>>(egraph: E, enode: &L) -> Self::Data;

    /// An optional hook that allows inspection before a [`union`] occurs.
    /// When explanations are enabled, it gives two ids that represent the two particular terms being unioned, not the canonical ids for the two eclasses.
    /// It also gives a justification for the union when explanations are enabled.
    ///
    /// By default it does nothing.
    ///
    /// `pre_union` is called _a lot_, so doing anything significant
    /// (like printing) will cause things to slow down.
    ///
    /// [`union`]: EGraph::union()
    #[allow(unused_variables)]
    fn pre_union<E: EGraphT<L, N = Self>>(
        egraph: E,
        id1: Id,
        id2: Id,
        justification: &Option<Justification>,
    ) {
    }

    /// Defines how to merge two `Data`s when their containing
    /// [`EClass`]es merge.
    ///
    /// This should update `a` to correspond to the merged analysis
    /// data.
    ///
    /// The result is a `DidMerge(a_merged, b_merged)` indicating whether
    /// the merged result is different from `a` and `b` respectively.
    ///
    /// Since `merge` can modify `a`, let `a0`/`a1` be the value of `a`
    /// before/after the call to `merge`, respectively.
    ///
    /// If `a0 != a1` the result must have `a_merged == true`. This may be
    /// conservative -- it may be `true` even if even if `a0 == a1`.
    ///
    /// If `b != a1` the result must have `b_merged == true`. This may be
    /// conservative -- it may be `true` even if even if `b == a1`.
    ///
    /// This function may modify the [`Analysis`], which can be useful as a way
    /// to store information for the [`crate::generic_analysis::Analysis::modify`] hook to process, since
    /// `modify` has access to the e-graph.
    fn merge(&mut self, a: &mut Self::Data, b: Self::Data) -> DidMerge;

    /// A hook that allows the modification of the
    /// [`EGraph`].
    ///
    /// By default this does nothing.
    ///
    /// This function is called immediately following
    /// `Analysis::merge` when unions are performed.
    #[allow(unused_variables)]
    fn modify<E: EGraphT<L, N = Self>>(egraph: E, id: Id) {}
}

impl<L: Language> LatticeAnalysis<L> for () {
    fn make<E: EGraphT<L, N = Self>>(_: E, _: &L) -> Self::Data {}

    fn merge(&mut self, _: &mut Self::Data, _: Self::Data) -> DidMerge {
        DidMerge(false, false)
    }
}

/// A utility for implementing [`Analysis::merge`]
/// when the `Data` type has a total ordering.
/// This will take the maximum of the two values.
pub fn merge_max<T: Ord>(to: &mut T, from: T) -> DidMerge {
    let cmp = (*to).cmp(&from);
    match cmp {
        Ordering::Less => {
            *to = from;
            DidMerge(true, false)
        }
        Ordering::Equal => DidMerge(false, false),
        Ordering::Greater => DidMerge(false, true),
    }
}

/// A utility for implementing [`Analysis::merge`]
/// when the `Data` type has a total ordering.
/// This will take the minimum of the two values.
pub fn merge_min<T: Ord>(to: &mut T, from: T) -> DidMerge {
    let cmp = (*to).cmp(&from);
    match cmp {
        Ordering::Less => DidMerge(false, true),
        Ordering::Equal => DidMerge(false, false),
        Ordering::Greater => {
            *to = from;
            DidMerge(true, false)
        }
    }
}

/// A utility for implementing [`Analysis::merge`]
/// when the `Data` type is an [`Option`].
///
/// Always take a `Some` over a `None`
/// and calls the given function to merge two `Some`s.
pub fn merge_option<T>(
    to: &mut Option<T>,
    from: Option<T>,
    merge_fn: impl FnOnce(&mut T, T) -> DidMerge,
) -> DidMerge {
    match (to.as_mut(), from) {
        (None, None) => DidMerge(false, false),
        (None, from @ Some(_)) => {
            *to = from;
            DidMerge(true, false)
        }
        (Some(_), None) => DidMerge(false, true),
        (Some(a), Some(b)) => merge_fn(a, b),
    }
}

/// Wrapper that converts a [`LatticeAnalysis`] into an [`Analysis`]
#[derive(Clone, Default)]
#[cfg_attr(feature = "serde-1", derive(serde::Serialize, serde::Deserialize))]
pub struct WrapLatticeAnalysis<N> {
    pub analysis: N,
    analysis_pending: UniqueQueue<Id>,
}

impl<N: Debug> Debug for WrapLatticeAnalysis<N> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        self.analysis.fmt(f)
    }
}

impl<L: Language, N: LatticeAnalysis<L>> AnalysisData<L> for WrapLatticeAnalysis<N> {
    type Data = N::Data;
}

struct ExtrA;

impl<N> Extractor<WrapLatticeAnalysis<N>> for ExtrA {
    type Out = N;

    fn proj(x: &WrapLatticeAnalysis<N>) -> &Self::Out {
        &x.analysis
    }

    fn proj_mut(x: &mut WrapLatticeAnalysis<N>) -> &mut Self::Out {
        &mut x.analysis
    }
}

impl<L: Language, N: LatticeAnalysis<L>> Analysis<L> for WrapLatticeAnalysis<N> {
    fn make<E: EGraphT<L, N = Self>>(mut egraph: E, enode: &L) -> Self::Data {
        N::make(egraph.shift::<ExtrA, ExtrId>(), enode)
    }

    fn post_make<E: EGraphT<L, N = Self>>(mut egraph: E, id: Id) {
        N::modify(egraph.shift::<ExtrA, ExtrId>(), id)
    }

    fn pre_union<E: EGraphT<L, N = Self>>(
        mut egraph: E,
        id1: Id,
        id2: Id,
        justification: &Option<Justification>,
    ) {
        N::pre_union(egraph.shift::<ExtrA, ExtrId>(), id1, id2, justification)
    }

    fn merge<E: EGraphT<L, N = Self>>(
        mut egraph: E,
        new_root: Id,
        _: Id,
        other_data: Self::Data,
        other_parents: &[Id],
        _: &Option<Justification>,
    ) {
        let (class, analysis, _) = egraph.class_and_rest(new_root);
        let analysis = E::proj_mut(analysis);
        let data = E::proj_data_mut(&mut class.data);
        let did_merge = analysis.analysis.merge(data, other_data);
        if did_merge.0 {
            analysis
                .analysis_pending
                .extend(class.parents.iter().copied());
        }
        if did_merge.1 {
            analysis
                .analysis_pending
                .extend(other_parents.iter().copied());
        }
        N::modify(egraph.shift::<ExtrA, ExtrId>(), new_root)
    }

    fn rebuild<E: EGraphT<L, N = Self>>(mut egraph: E, _: bool) -> bool {
        let mut analysis_pending = mem::take(&mut egraph.analysis_mut().analysis_pending);
        if analysis_pending.is_empty() {
            return false;
        }

        while let Some(class_id) = analysis_pending.pop() {
            let node = egraph.id_to_node(class_id).clone();
            let node_data = N::make(egraph.shift::<ExtrA, ExtrId>(), &node);
            let (class, analysis, _) = egraph.class_and_rest(class_id);
            let analysis = E::proj_mut(analysis);
            let did_merge = analysis
                .analysis
                .merge(E::proj_data_mut(&mut class.data), node_data);
            if did_merge.0 {
                analysis
                    .analysis_pending
                    .extend(class.parents.iter().copied());
                N::modify(egraph.shift::<ExtrA, ExtrId>(), class_id)
            }
        }
        true
    }
}

impl<L: Language, N: LatticeAnalysis<L>, O: Analysis<L>> EGraph<L, (WrapLatticeAnalysis<N>, O)> {
    /// Update the analysis data of an e-class.
    ///
    /// This also propagates the changes through the e-graph,
    /// so [`Analysis::make`] and [`Analysis::merge`] will get
    /// called for other parts of the e-graph on rebuild.
    pub fn set_analysis_data(&mut self, id: Id, new_data: N::Data) {
        let (class, analysis, _) = self.class_and_rest(id);
        class.data.0 = new_data;
        analysis.0.analysis_pending.extend(class.parents());
        N::modify(
            Just::new(self)
                .shift::<Extr0, Extr0>()
                .shift::<ExtrA, ExtrId>(),
            id,
        )
    }
}
