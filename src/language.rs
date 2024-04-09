use std::ops::BitOr;
use std::{cmp::Ordering, convert::TryFrom};
use std::{
    convert::Infallible,
    fmt::{self, Debug, Display},
};
use std::{hash::Hash, str::FromStr};

use crate::*;

pub use crate::raw::language::*;
use fmt::Formatter;
use symbolic_expressions::{Sexp, SexpError};
use thiserror::Error;

/// A trait for parsing e-nodes. This is implemented automatically by
/// [`define_language!`].
///
/// If a [`Language`] implements both [`Display`] and [`FromOp`], the
/// [`Display`] implementation should produce a string suitable for parsing by
/// [`from_op`]:
///
/// ```
/// # use egg::*;
/// # use std::fmt::Display;
/// fn from_op_display_compatible<T: FromOp + Display>(node: T) {
///     let op = node.to_string();
///     let mut children = Vec::new();
///     node.for_each(|id| children.push(id));
///     let parsed = T::from_op(&op, children).unwrap();
///
///     assert_eq!(node, parsed);
/// }
/// ```
///
/// # Examples
/// `define_language!` implements [`FromOp`] and [`Display`] automatically:
/// ```
/// # use egg::*;
///
/// define_language! {
///     enum Calc {
///        "+" = Add([Id; 2]),
///        Num(i32),
///     }
/// }
///
/// let add = Calc::Add([Id::from(0), Id::from(1)]);
/// let parsed = Calc::from_op("+", vec![Id::from(0), Id::from(1)]).unwrap();
///
/// assert_eq!(add.to_string(), "+");
/// assert_eq!(parsed, add);
/// ```
///
/// [`from_op`]: FromOp::from_op
pub trait FromOp: Language + Sized {
    /// The error type returned by [`from_op`] if its arguments do not
    /// represent a valid e-node.
    ///
    /// [`from_op`]: FromOp::from_op
    type Error: Debug;

    /// Parse an e-node with operator `op` and children `children`.
    fn from_op(op: &str, children: Vec<Id>) -> Result<Self, Self::Error>;
}

/// A generic error for failing to parse an operator. This is the error type
/// used by [`define_language!`] for [`FromOp::Error`], and is a sensible choice
/// when implementing [`FromOp`] manually.
#[derive(Debug, Error)]
#[error("could not parse an e-node with operator {op:?} and children {children:?}")]
pub struct FromOpError {
    op: String,
    children: Vec<Id>,
}

impl FromOpError {
    /// Create a new `FromOpError` representing a failed call
    /// `FromOp::from_op(op, children)`.
    pub fn new(op: &str, children: Vec<Id>) -> Self {
        Self {
            op: op.to_owned(),
            children,
        }
    }
}

/// A marker that defines acceptable children types for [`define_language!`].
///
/// See [`define_language!`] for more details.
/// You should not have to implement this trait.
///
pub trait LanguageChildren {
    /// Checks if there are no children.
    fn is_empty(&self) -> bool {
        self.len() == 0
    }
    /// Returns the number of children.
    fn len(&self) -> usize;
    /// Checks if n is an acceptable number of children for this type.
    fn can_be_length(n: usize) -> bool;
    /// Create an instance of this type from a `Vec<Id>`,
    /// with the guarantee that can_be_length is already true on the `Vec`.
    fn from_vec(v: Vec<Id>) -> Self;
    /// Returns a slice of the children `Id`s.
    fn as_slice(&self) -> &[Id];
    /// Returns a mutable slice of the children `Id`s.
    fn as_mut_slice(&mut self) -> &mut [Id];
}

impl<const N: usize> LanguageChildren for [Id; N] {
    fn len(&self) -> usize {
        N
    }

    fn can_be_length(n: usize) -> bool {
        n == N
    }

    fn from_vec(v: Vec<Id>) -> Self {
        Self::try_from(v.as_slice()).unwrap()
    }

    fn as_slice(&self) -> &[Id] {
        self
    }

    fn as_mut_slice(&mut self) -> &mut [Id] {
        self
    }
}

#[rustfmt::skip]
impl LanguageChildren for Box<[Id]> {
    fn len(&self) -> usize                   { <[Id]>::len(self) }
    fn can_be_length(_: usize) -> bool       { true }
    fn from_vec(v: Vec<Id>) -> Self          { v.into() }
    fn as_slice(&self) -> &[Id]              { self }
    fn as_mut_slice(&mut self) -> &mut [Id]  { self }
}

#[rustfmt::skip]
impl LanguageChildren for Vec<Id> {
    fn len(&self) -> usize                   { <[Id]>::len(self) }
    fn can_be_length(_: usize) -> bool       { true }
    fn from_vec(v: Vec<Id>) -> Self          { v }
    fn as_slice(&self) -> &[Id]              { self }
    fn as_mut_slice(&mut self) -> &mut [Id]  { self }
}

#[rustfmt::skip]
impl LanguageChildren for Id {
    fn len(&self) -> usize                   { 1 }
    fn can_be_length(n: usize) -> bool       { n == 1 }
    fn from_vec(v: Vec<Id>) -> Self          { v[0] }
    fn as_slice(&self) -> &[Id]              { std::slice::from_ref(self) }
    fn as_mut_slice(&mut self) -> &mut [Id]  { std::slice::from_mut(self) }
}

#[cfg(feature = "serde-1")]
impl<L: Language + Display> serde::Serialize for RecExpr<L> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        let s = self.to_sexp().to_string();
        serializer.serialize_str(&s)
    }
}

impl<L: Language + Display> Display for RecExpr<L> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.nodes.is_empty() {
            Display::fmt("()", f)
        } else {
            let s = self.to_sexp().to_string();
            Display::fmt(&s, f)
        }
    }
}

impl<L: Language> RecExpr<L> {
    pub(crate) fn extract(&self, new_root: Id) -> Self {
        self[new_root].build_recexpr(|id| self[id].clone())
    }
    pub(crate) fn compact(mut self) -> Self {
        let mut ids = HashMap::<Id, Id>::default();
        let mut set = IndexSet::default();
        for (i, node) in self.nodes.drain(..).enumerate() {
            let node = node.map_children(|id| ids[&id]);
            let new_id = set.insert_full(node).0;
            ids.insert(Id::from(i), Id::from(new_id));
        }
        self.nodes.extend(set);
        self
    }
}

impl<L: Language + Display> RecExpr<L> {
    /// Convert this RecExpr into an Sexp
    pub(crate) fn to_sexp(&self) -> Sexp {
        let last = self.nodes.len() - 1;
        if !self.is_dag() {
            log::warn!("Tried to print a non-dag: {:?}", self.nodes);
        }
        self.to_sexp_rec(last, &mut |_| None)
    }

    fn to_sexp_rec(&self, i: usize, f: &mut impl FnMut(usize) -> Option<String>) -> Sexp {
        let node = &self.nodes[i];
        let op = Sexp::String(node.to_string());
        if node.is_leaf() {
            op
        } else {
            let mut vec = vec![op];
            for child in node.children().iter().map(|i| usize::from(*i)) {
                vec.push(if let Some(s) = f(child) {
                    return Sexp::String(s);
                } else if child < i {
                    self.to_sexp_rec(child, f)
                } else {
                    Sexp::String(format!("<<<< CYCLE to {} = {:?} >>>>", i, node))
                })
            }
            Sexp::List(vec)
        }
    }

    /// Pretty print with a maximum line length.
    ///
    /// This gives you a nice, indented, pretty-printed s-expression.
    ///
    /// # Example
    /// ```
    /// # use egg::*;
    /// let e: RecExpr<SymbolLang> = "(* (+ 2 2) (+ x y))".parse().unwrap();
    /// assert_eq!(e.pretty(10), "
    /// (*
    ///   (+ 2 2)
    ///   (+ x y))
    /// ".trim());
    /// ```
    pub fn pretty(&self, width: usize) -> String {
        let sexp = self.to_sexp();

        let mut buf = String::new();
        pretty_print(&mut buf, &sexp, width, 1).unwrap();
        buf
    }
}

/// An error type for failures when attempting to parse an s-expression as a
/// [`RecExpr<L>`].
#[derive(Debug, Error)]
pub enum RecExprParseError<E> {
    /// An empty s-expression was found. Usually this is caused by an
    /// empty list "()" somewhere in the input.
    #[error("found empty s-expression")]
    EmptySexp,

    /// A list was found where an operator was expected. This is caused by
    /// s-expressions of the form "((a b c) d e f)."
    #[error("found a list in the head position: {0}")]
    HeadList(Sexp),

    /// Attempting to parse an operator into a value of type `L` failed.
    #[error(transparent)]
    BadOp(E),

    /// An error occurred while parsing the s-expression itself, generally
    /// because the input had an invalid structure (e.g. unpaired parentheses).
    #[error(transparent)]
    BadSexp(SexpError),
}

impl<L: FromOp> FromStr for RecExpr<L> {
    type Err = RecExprParseError<L::Error>;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        use RecExprParseError::*;

        fn parse_sexp_into<L: FromOp>(
            sexp: &Sexp,
            expr: &mut RecExpr<L>,
        ) -> Result<Id, RecExprParseError<L::Error>> {
            match sexp {
                Sexp::Empty => Err(EmptySexp),
                Sexp::String(s) => {
                    let node = L::from_op(s, vec![]).map_err(BadOp)?;
                    Ok(expr.add(node))
                }
                Sexp::List(list) if list.is_empty() => Err(EmptySexp),
                Sexp::List(list) => match &list[0] {
                    Sexp::Empty => unreachable!("Cannot be in head position"),
                    list @ Sexp::List(..) => Err(HeadList(list.to_owned())),
                    Sexp::String(op) => {
                        let arg_ids: Vec<Id> = list[1..]
                            .iter()
                            .map(|s| parse_sexp_into(s, expr))
                            .collect::<Result<_, _>>()?;
                        let node = L::from_op(op, arg_ids).map_err(BadOp)?;
                        Ok(expr.add(node))
                    }
                },
            }
        }

        let mut expr = RecExpr::default();
        let sexp = symbolic_expressions::parser::parse_str(s.trim()).map_err(BadSexp)?;
        parse_sexp_into(&sexp, &mut expr)?;
        Ok(expr)
    }
}

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
use egg::{*, rewrite as rw};

define_language! {
    enum SimpleMath {
        "+" = Add([Id; 2]),
        "*" = Mul([Id; 2]),
        Num(i32),
        Symbol(Symbol),
    }
}

// in this case, our analysis itself doesn't require any data, so we can just
// use a unit struct and derive Default
#[derive(Default)]
struct ConstantFolding;
impl Analysis<SimpleMath> for ConstantFolding {
    type Data = Option<i32>;

    fn merge(&mut self, to: &mut Self::Data, from: Self::Data) -> DidMerge {
        egg::merge_max(to, from)
    }

    fn make(egraph: &mut EGraph<SimpleMath, Self>, enode: &SimpleMath) -> Self::Data {
        let x = |i: &Id| egraph[*i].data;
        match enode {
            SimpleMath::Num(n) => Some(*n),
            SimpleMath::Add([a, b]) => Some(x(a)? + x(b)?),
            SimpleMath::Mul([a, b]) => Some(x(a)? * x(b)?),
            _ => None,
        }
    }

    fn modify(egraph: &mut EGraph<SimpleMath, Self>, id: Id) {
        if let Some(i) = egraph[id].data {
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
pub trait Analysis<L: Language>: Sized {
    /// The per-[`EClass`] data for this analysis.
    type Data: Debug + Clone;

    /// Makes a new [`Analysis`] data for a given e-node.
    ///
    /// Note the mutable `egraph` parameter: this is needed for some
    /// advanced use cases, but most use cases will not need to mutate
    /// the e-graph in any way.
    /// It is **not** `make`'s responsiblity to insert the e-node;
    /// the e-node is "being inserted" when this function is called.
    /// Doing so will create an infinite loop.
    fn make(egraph: &mut EGraph<L, Self>, enode: &L) -> Self::Data;

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
    fn pre_union(
        egraph: &EGraph<L, Self>,
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
    /// to store information for the [`Analysis::modify`] hook to process, since
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
    fn modify(egraph: &mut EGraph<L, Self>, id: Id) {}

    /// A hook called at the start of [`EGraph::push`]
    #[allow(unused_variables)]
    fn pre_push(egraph: &mut EGraph<L, Self>) {}

    /// A hook called at the end of [`EGraph::pop_n`]
    #[allow(unused_variables)]
    fn post_pop_n(egraph: &mut EGraph<L, Self>, n: usize) {}
}

impl<L: Language> Analysis<L> for () {
    type Data = ();
    fn make(_egraph: &mut EGraph<L, Self>, _enode: &L) -> Self::Data {}
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

/// A simple language used for testing.
#[derive(Debug, Hash, PartialEq, Eq, Clone, PartialOrd, Ord)]
#[cfg_attr(feature = "serde-1", derive(serde::Serialize, serde::Deserialize))]
pub struct SymbolLang {
    /// The operator for an enode
    pub op: Symbol,
    /// The enode's children `Id`s
    pub children: Vec<Id>,
}

impl SymbolLang {
    /// Create an enode with the given string and children
    pub fn new(op: impl Into<Symbol>, children: Vec<Id>) -> Self {
        let op = op.into();
        Self { op, children }
    }

    /// Create childless enode with the given string
    pub fn leaf(op: impl Into<Symbol>) -> Self {
        Self::new(op, vec![])
    }
}

impl Language for SymbolLang {
    type Discriminant = Symbol;

    fn discriminant(&self) -> Self::Discriminant {
        self.op
    }

    fn matches(&self, other: &Self) -> bool {
        self.op == other.op && self.len() == other.len()
    }

    fn children(&self) -> &[Id] {
        &self.children
    }

    fn children_mut(&mut self) -> &mut [Id] {
        &mut self.children
    }
}

impl Display for SymbolLang {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        Display::fmt(&self.op, f)
    }
}

impl FromOp for SymbolLang {
    type Error = Infallible;

    fn from_op(op: &str, children: Vec<Id>) -> Result<Self, Self::Error> {
        Ok(Self {
            op: op.into(),
            children,
        })
    }
}
