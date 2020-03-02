use std::fmt::Debug;
use std::iter::ExactSizeIterator;

use crate::{
    unionfind::{Key, UnionFind, Value},
    EGraph, ENode, Id, Language,
};

/** Arbitrary data associated with an [`EClass`].

`egg` allows you to associate arbitrary data with each eclass.
The [`Metadata`] allows that data to behave well even across eclasses merges.

[`Metadata`] can prove useful in many situtations.
One common one is constant folding, a kind of partial evaluation.
In that case, the metadata is basically `Option<L>`, storing
the cheapest constant expression (if any) that's equivalent to the
enodes in this eclass.
See the test files [`math.rs`] and [`prop.rs`] for more complex
examples on this usage of [`Metadata`].

If you don't care about [`Metadata`], `()` implements it trivally,
just use that.

# Example

```
use egg::{*, rewrite as rw};

define_language! {
    enum EasyMath {
        Num(i32),
        Add = "+",
        Mul = "*",
        Variable(String),
    }
}

use EasyMath::*;
type Meta = Option<i32>;

impl Metadata<EasyMath> for Meta {
    type Error = ();
    fn merge(&self, other: &Self) -> Self {
        self.clone().and(other.clone())
    }
    fn make(egraph: &EGraph<EasyMath, Self>, enode: &ENode<EasyMath>) -> Self {
         let c = |i: usize| {
             let eclass = &egraph[enode.children[i]];
             eclass.metadata.clone()
         };
         match enode.op {
             Num(i) => Some(i),
             Add => Some(c(0)? + c(1)?),
             Mul => Some(c(0)? * c(1)?),
             _ => None,
         }
    }
    fn modify(eclass: &mut EClass<EasyMath, Self>) {
        if let Some(i) = eclass.metadata {
            eclass.nodes.push(enode!(Num(i)))
        }
    }
}

let rules: &[Rewrite<EasyMath, Meta>] = &[
    rw!("commute-add"; "(+ ?a ?b)" => "(+ ?b ?a)"),
    rw!("commute-mul"; "(* ?a ?b)" => "(* ?b ?a)"),

    rw!("add-0"; "(+ ?a 0)" => "?a"),
    rw!("mul-0"; "(* ?a 0)" => "0"),
    rw!("mul-1"; "(* ?a 1)" => "?a"),
];

let expr = "(+ 0 (* (+ 4 -3) foo))".parse().unwrap();
let mut runner = Runner::new().with_expr(&expr).run(&rules);
let just_foo = runner.egraph.add(enode!(Variable("foo".into())));
assert_eq!(runner.egraph.find(runner.roots[0]), runner.egraph.find(just_foo));
```

[`Metadata`]: trait.Metadata.html
[`EClass`]: struct.EClass.html
[`ENode`]: struct.ENode.html
[`math.rs`]: https://github.com/mwillsey/egg/blob/master/tests/math.rs
[`prop.rs`]: https://github.com/mwillsey/egg/blob/master/tests/prop.rs
*/
pub trait Metadata<L>: Sized + Debug + PartialEq + Eq {
    /// Unused for now, probably just make this `()`.
    type Error: Debug;

    /// Defines how to merge two [`Metadata`]s when their containing
    /// [`EClass`]es merge.
    ///
    /// [`Metadata`]: trait.Metadata.html
    /// [`EClass`]: struct.EClass.html
    fn merge(&self, other: &Self) -> Self;

    /// Makes a new [`Metadata`] given an operator and its children
    /// [`Metadata`].
    ///
    /// [`Metadata`]: trait.Metadata.html
    fn make(egraph: &EGraph<L, Self>, enode: &ENode<L>) -> Self;

    /// A hook that allow a [`Metadata`] to modify its containing
    /// [`EClass`].
    ///
    /// By default this does nothing.
    ///
    /// [`Metadata`]: trait.Metadata.html
    /// [`EClass`]: struct.EClass.html
    fn modify(_eclass: &mut EClass<L, Self>) {}
}

impl<L: Language> Metadata<L> for () {
    type Error = std::convert::Infallible;
    fn merge(&self, _other: &()) {}
    fn make(_: &EGraph<L, Self>, _: &ENode<L>) {}
}

/// An equivalence class of [`ENode`]s
///
/// [`ENode`]: struct.ENode.html
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct EClass<L, M> {
    /// This eclass's id.
    pub id: Id,
    /// The equivalent enodes in this equivalence class.
    pub nodes: Vec<ENode<L>>,
    /// The metadata associated with this eclass.
    pub metadata: M,
    #[cfg(feature = "parent-pointers")]
    #[doc(hidden)]
    pub(crate) parents: indexmap::IndexSet<usize>,
}

impl<L, M> EClass<L, M> {
    /// Returns `true` if the `eclass` is empty.
    pub fn is_empty(&self) -> bool {
        self.nodes.is_empty()
    }

    /// Returns the number of enodes in this eclass.
    pub fn len(&self) -> usize {
        self.nodes.len()
    }

    /// Iterates over the enodes in the this eclass.
    pub fn iter(&self) -> impl ExactSizeIterator<Item = &ENode<L>> {
        self.nodes.iter()
    }
}

impl<L: Language, M: Metadata<L>> Value for EClass<L, M> {
    type Error = std::convert::Infallible;
    fn merge<K: Key>(
        _unionfind: &mut UnionFind<K, Self>,
        to: Self,
        from: Self,
    ) -> Result<Self, Self::Error> {
        let mut less = to.nodes;
        let mut more = from.nodes;

        // make sure less is actually smaller
        if more.len() < less.len() {
            std::mem::swap(&mut less, &mut more);
        }

        more.extend(less);

        let mut eclass = EClass {
            id: to.id,
            nodes: more,
            metadata: to.metadata.merge(&from.metadata),
            #[cfg(feature = "parent-pointers")]
            parents: {
                let mut parents = to.parents;
                parents.extend(from.parents);
                parents
            },
        };

        M::modify(&mut eclass);
        Ok(eclass)
    }
}
