use crate::{EGraph, Id, Justification, Language};
use std::fmt::Debug;
use std::marker::PhantomData;
use std::ops::{Deref, DerefMut};

pub trait Extractor<X>: 'static {
    type Out;

    fn proj(x: &X) -> &Self::Out;

    fn proj_mut(x: &mut X) -> &mut Self::Out;
}

/// An [`EGraph`] that is focusing on a specific sub [`Analysis`]
///
/// It implements [`DerefMut`] to extract the underlying [`EGraph`] and includes methods
/// to convert the full [`Analysis`] from the [`EGraph`] to the specific sub [`Analysis`]
pub trait EGraphT<L: Language>: DerefMut<Target = EGraph<L, Self::A>> + Sized {
    /// The full [`Analysis`] of the [`EGraph`]
    type A: Analysis<L>;

    /// The sub [`Analysis`] being focused on
    type N: AnalysisData<L>;
    type E: Extractor<Self::A, Out = Self::N>;

    type ED: Extractor<<Self::A as AnalysisData<L>>::Data, Out = <Self::N as AnalysisData<L>>::Data>;
    fn proj(x: &Self::A) -> &Self::N {
        Self::E::proj(x)
    }
    fn proj_mut(x: &mut Self::A) -> &mut Self::N {
        Self::E::proj_mut(x)
    }

    fn proj_data(x: &<Self::A as AnalysisData<L>>::Data) -> &<Self::N as AnalysisData<L>>::Data {
        Self::ED::proj(x)
    }

    fn proj_data_mut(
        x: &mut <Self::A as AnalysisData<L>>::Data,
    ) -> &mut <Self::N as AnalysisData<L>>::Data {
        Self::ED::proj_mut(x)
    }

    fn analysis<'a>(&'a self) -> &'a Self::N
    where
        L: 'a,
    {
        Self::proj(&self.analysis)
    }

    fn analysis_mut<'a>(&'a mut self) -> &'a mut Self::N
    where
        L: 'a,
    {
        Self::proj_mut(&mut self.analysis)
    }

    fn data<'a>(&'a self, id: Id) -> &'a <Self::N as AnalysisData<L>>::Data
    where
        L: 'a,
    {
        Self::proj_data(&self[id].data)
    }

    fn data_mut<'a>(&'a mut self, id: Id) -> &'a mut <Self::N as AnalysisData<L>>::Data
    where
        L: 'a,
    {
        Self::proj_data_mut(&mut self[id].data)
    }

    fn shift<E, ED>(
        &mut self,
    ) -> EGraphC<'_, EGraph<L, Self::A>, ExtrCompose<Self::E, E>, ExtrCompose<Self::ED, ED>> {
        EGraphC::new(&mut **self)
    }
}

pub struct EGraphC<'a, T, E, ED>(&'a mut T, PhantomData<(E, ED)>);

impl<'a, T, E, ED> Deref for EGraphC<'a, T, E, ED> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<'a, T, E, ED> DerefMut for EGraphC<'a, T, E, ED> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl<'a, L: Language, N: Analysis<L>, E: Extractor<N>, ED> EGraphT<L>
    for EGraphC<'a, EGraph<L, N>, E, ED>
where
    E::Out: AnalysisData<L>,
    ED: Extractor<N::Data, Out = <E::Out as AnalysisData<L>>::Data>,
{
    type A = N;
    type N = E::Out;

    type E = E;

    type ED = ED;
}

impl<'a, T, E, ED> EGraphC<'a, T, E, ED> {
    pub fn new(t: &'a mut T) -> Self {
        EGraphC(t, PhantomData)
    }
}

pub(crate) struct ExtrId;

impl<X> Extractor<X> for ExtrId {
    type Out = X;

    fn proj(x: &X) -> &Self::Out {
        x
    }

    fn proj_mut(x: &mut X) -> &mut Self::Out {
        x
    }
}

pub(crate) type Just<'a, T> = EGraphC<'a, T, ExtrId, ExtrId>;

pub struct ExtrCompose<E, F>(E, F);

impl<X, E: Extractor<X>, F: Extractor<E::Out>> Extractor<X> for ExtrCompose<E, F> {
    type Out = F::Out;

    fn proj(x: &X) -> &Self::Out {
        F::proj(E::proj(x))
    }

    fn proj_mut(x: &mut X) -> &mut Self::Out {
        F::proj_mut(E::proj_mut(x))
    }
}

pub(crate) struct Extr0;

impl<X, Y> Extractor<(X, Y)> for Extr0 {
    type Out = X;

    fn proj(x: &(X, Y)) -> &Self::Out {
        &x.0
    }

    fn proj_mut(x: &mut (X, Y)) -> &mut Self::Out {
        &mut x.0
    }
}

pub(crate) struct Extr1;

impl<X, Y> Extractor<(X, Y)> for Extr1 {
    type Out = Y;

    fn proj(x: &(X, Y)) -> &Self::Out {
        &x.1
    }

    fn proj_mut(x: &mut (X, Y)) -> &mut Self::Out {
        &mut x.1
    }
}

/// Contains the `Data` associated type for [`Analysis`] and [`LatticeAnalysis`]
pub trait AnalysisData<L: Language>: Sized {
    /// The per-[`EClass`] data for this analysis.
    type Data: Debug;
}

/** Arbitrary data associated with an [`EClass`].

[`Analysis`] allows you to associate arbitrary data with each eclass.

It is also useful for providing hooks to stay consistent with various [`EGraph`] operations

If you don't care about [`Analysis`], `()` implements it trivally, just use that.
If you want to use multiple [`Analysis`], it is also implemented for pairs
 **/
#[allow(unused_variables)]
pub trait Analysis<L: Language>: AnalysisData<L> {
    /// Makes a new [`Analysis`] data for a given e-node.
    ///
    /// Note the mutable `egraph` parameter: this is needed for some
    /// advanced use cases, but most use cases will not need to mutate
    /// the e-graph in any way.
    /// It is **not** `make`'s responsiblity to insert the e-node;
    /// the e-node is "being inserted" when this function is called.
    /// Doing so will create an infinite loop.
    fn make<E: EGraphT<L, N = Self>>(egraph: E, enode: &L) -> Self::Data;

    /// An optional hook that allows the modifications involving the `Id` of newly created nodes
    fn post_make<E: EGraphT<L, N = Self>>(egraph: E, id: Id) {}

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
    fn pre_union<E: EGraphT<L, N = Self>>(
        egraph: E,
        id1: Id,
        id2: Id,
        justification: &Option<Justification>,
    ) {
    }

    /// Hook called just after two [`EClass`]es merge.
    /// It also gives a justification for the union when explanations are enabled.
    ///
    /// `new_root` contains the `Id` of the [`EClass`] that was chosen as the parent
    /// and can be used to lookup that [`EClass`] in the [`EGraph`]
    ///
    /// `other_id`, `other_data`, and `other_parents` represent the other [`EClass`]
    /// since it is no longer available in the [`EGraph`]
    ///
    /// This should update `egraph.node(new_root)` to correspond to the merged analysis data.
    fn merge<E: EGraphT<L, N = Self>>(
        egraph: E,
        new_root: Id,
        other_id: Id,
        other_data: Self::Data,
        other_parents: &[Id],
        justification: &Option<Justification>,
    ) {
    }

    /// Hook called when rebuilding the [`EGraph`]
    ///
    /// Should return `true` if it did any work causes this rebuild to restart after it finishes
    ///
    /// If `will_repeat` is true this function will necessarily be called again in this rebuild cycle
    fn rebuild<E: EGraphT<L, N = Self>>(egraph: E, will_repeat: bool) -> bool {
        false
    }
}

impl<L: Language> AnalysisData<L> for () {
    type Data = ();
}

impl<L: Language> Analysis<L> for () {
    fn make<E: EGraphT<L, N = Self>>(_: E, _: &L) -> Self::Data {}
}

impl<L: Language, N0: AnalysisData<L>, N1: AnalysisData<L>> AnalysisData<L> for (N0, N1) {
    type Data = (N0::Data, N1::Data);
}

impl<L: Language, N0: Analysis<L>, N1: Analysis<L>> Analysis<L> for (N0, N1) {
    fn make<E: EGraphT<L, N = Self>>(mut egraph: E, enode: &L) -> Self::Data {
        (
            N0::make(egraph.shift::<Extr0, Extr0>(), enode),
            N1::make(egraph.shift::<Extr1, Extr1>(), enode),
        )
    }

    fn post_make<E: EGraphT<L, N = Self>>(mut egraph: E, id: Id) {
        N0::post_make(egraph.shift::<Extr0, Extr0>(), id);
        N1::post_make(egraph.shift::<Extr1, Extr1>(), id);
    }

    fn pre_union<E: EGraphT<L, N = Self>>(
        mut egraph: E,
        id1: Id,
        id2: Id,
        justification: &Option<Justification>,
    ) {
        N0::pre_union(egraph.shift::<Extr0, Extr0>(), id1, id2, justification);
        N1::pre_union(egraph.shift::<Extr1, Extr1>(), id1, id2, justification);
    }

    fn merge<E: EGraphT<L, N = Self>>(
        mut egraph: E,
        new_root: Id,
        other_id: Id,
        other_data: Self::Data,
        other_parents: &[Id],
        justification: &Option<Justification>,
    ) {
        N0::merge(
            egraph.shift::<Extr0, Extr0>(),
            new_root,
            other_id,
            other_data.0,
            other_parents,
            justification,
        );
        N1::merge(
            egraph.shift::<Extr1, Extr1>(),
            new_root,
            other_id,
            other_data.1,
            other_parents,
            justification,
        );
    }

    fn rebuild<E: EGraphT<L, N = Self>>(mut egraph: E, will_repeat: bool) -> bool {
        let x = N0::rebuild(egraph.shift::<Extr0, Extr0>(), will_repeat);
        N1::rebuild(egraph.shift::<Extr1, Extr1>(), will_repeat || x) || x
    }
}
