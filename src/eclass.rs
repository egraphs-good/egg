use std::fmt::{self, Debug};
use std::iter::ExactSizeIterator;

use crate::{ENode, Id, Language};

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

impl_enode! {
    enum Op {
        "+" = Add(Id, Id),
        "*" = Mul(Id, Id),
        Num(i32),
        Variable(String),
    }
}

#[derive(Default)]
struct EasyMath;
impl Language for EasyMath {
    type ENode = Op;
    type Metadata = Option<i32>;

    fn metadata_merge(&self, to: &mut Self::Metadata, from: Self::Metadata) -> bool {
        if to.is_none() && from.is_some() {
            *to = from;
            true
        } else {
            false
        }
    }

    fn metadata_make(egraph: &mut EGraph<Self>, enode: &Self::ENode) -> Self::Metadata {
        let x = |i: &Id| egraph[*i].metadata;
        match enode {
            Op::Num(n) => Some(*n),
            Op::Add(a, b) => Some(x(a)? + x(b)?),
            Op::Mul(a, b) => Some(x(a)? * x(b)?),
            _ => None,
        }
    }

    fn metadata_modify(egraph: &mut EGraph<Self>, id: Id) {
        if let Some(i) = egraph[id].metadata {
            let added = egraph.add(Op::Num(i));
            egraph.union(id, added);
        }
    }
}

let rules: &[Rewrite<EasyMath>] = &[
    rw!("commute-add"; "(+ ?a ?b)" => "(+ ?b ?a)"),
    rw!("commute-mul"; "(* ?a ?b)" => "(* ?b ?a)"),

    rw!("add-0"; "(+ ?a 0)" => "?a"),
    rw!("mul-0"; "(* ?a 0)" => "0"),
    rw!("mul-1"; "(* ?a 1)" => "?a"),
];

let expr = "(+ 0 (* (+ 4 -3) foo))".parse().unwrap();
let mut runner = Runner::default().with_expr(&expr).run(&rules);
let just_foo = runner.egraph.add_expr(&"foo".parse().unwrap());
assert_eq!(runner.egraph.find(runner.roots[0]), runner.egraph.find(just_foo));
```

[`Metadata`]: trait.Metadata.html
[`EClass`]: struct.EClass.html
[`ENode`]: struct.ENode.html
[`math.rs`]: https://github.com/mwillsey/egg/blob/master/tests/math.rs
[`prop.rs`]: https://github.com/mwillsey/egg/blob/master/tests/prop.rs
*/

/// An equivalence class of [`ENode`]s
///
/// [`ENode`]: trait.ENode.html
#[non_exhaustive]
#[derive(Clone)]
pub struct EClass<L: Language> {
    /// This eclass's id.
    pub id: Id,
    /// The equivalent enodes in this equivalence class.
    pub nodes: Vec<L::ENode>,
    /// The metadata associated with this eclass.
    pub metadata: L::Metadata,
    pub(crate) parents: Vec<(L::ENode, Id)>,
}

impl<L: Language> Debug for EClass<L> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("EClass")
            .field("id", &self.id)
            .field("nodes", &self.nodes)
            .field("metadata", &self.metadata)
            .field("parents", &self.parents)
            .finish()
    }
}

impl<L: Language> EClass<L> {
    /// Returns `true` if the `eclass` is empty.
    pub fn is_empty(&self) -> bool {
        self.nodes.is_empty()
    }

    /// Returns the number of enodes in this eclass.
    pub fn len(&self) -> usize {
        self.nodes.len()
    }

    /// Iterates over the enodes in this eclass.
    pub fn iter(&self) -> impl ExactSizeIterator<Item = &L::ENode> {
        self.nodes.iter()
    }

    /// Iterates over the childless enodes in this eclass.
    pub fn leaves(&self) -> impl Iterator<Item = &L::ENode> {
        self.nodes.iter().filter(|&n| n.is_leaf())
    }

    /// Asserts that the childless enodes in this eclass are unique.
    pub fn assert_unique_leaves(&self)
    where
        L: Language,
    {
        let mut leaves = self.leaves();
        if let Some(first) = leaves.next() {
            assert!(
                leaves.all(|l| l == first),
                "Different leaves in eclass {}: {:?}",
                self.id,
                self.leaves().collect::<indexmap::IndexSet<_>>()
            );
        }
    }
}
