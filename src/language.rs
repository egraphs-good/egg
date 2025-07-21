use std::borrow::{Borrow, BorrowMut};
use std::iter::FromIterator;
use std::ops::{BitOr, Deref, DerefMut, Index, IndexMut};
use std::{cmp::Ordering, convert::TryFrom};
use std::{
    convert::Infallible,
    fmt::{self, Debug, Display},
};
use std::{hash::Hash, str::FromStr};

use crate::*;

use fmt::Formatter;
use symbolic_expressions::{Sexp, SexpError};
use thiserror::Error;

/// Trait that defines a Language whose terms will be in the [`EGraph`].
///
/// Check out the [`define_language!`] macro for an easy way to create
/// a [`Language`].
///
/// If you want to pretty-print expressions, you should implement [`Display`] to
/// display the language node's operator. For example, a language node
/// `Add([Id; 2])` might be displayed as "+".
///
/// To parse expressions from strings you should also implement [`FromOp`].
///
/// The [`define_language!`] macro automatically implements both [`Display`] and
/// [`FromOp`].
///
/// See [`SymbolLang`] for quick-and-dirty use cases.
#[allow(clippy::len_without_is_empty)]
pub trait Language: Debug + Clone + Eq + Ord + Hash {
    /// Type representing the cases of this language.
    ///
    /// Used for short-circuiting the search for equivalent nodes.
    type Discriminant: Debug + Clone + Eq + Hash;

    /// Return the `Discriminant` of this node.
    #[allow(enum_intrinsics_non_enums)]
    fn discriminant(&self) -> Self::Discriminant;

    /// Returns true if this enode matches another enode.
    /// This should only consider the operator and the arity,
    /// not the children `Id`s.
    fn matches(&self, other: &Self) -> bool;

    /// Returns the children of this e-node.
    fn children(&self) -> &[Id];

    /// Returns a mutable slice of the children of this e-node.
    fn children_mut(&mut self) -> &mut [Id];

    /// Runs a given function on each child `Id`.
    fn for_each<F: FnMut(Id)>(&self, f: F) {
        self.children().iter().copied().for_each(f)
    }

    /// Runs a given function on each child `Id`, allowing mutation of that `Id`.
    fn for_each_mut<F: FnMut(&mut Id)>(&mut self, f: F) {
        self.children_mut().iter_mut().for_each(f)
    }

    /// Runs a falliable function on each child, stopping if the function returns
    /// an error.
    fn try_for_each<E, F>(&self, mut f: F) -> Result<(), E>
    where
        F: FnMut(Id) -> Result<(), E>,
    {
        self.fold(Ok(()), |res, id| res.and_then(|_| f(id)))
    }

    /// Returns the number of the children this enode has.
    ///
    /// The default implementation uses `fold` to accumulate the number of
    /// children.
    fn len(&self) -> usize {
        self.fold(0, |len, _| len + 1)
    }

    /// Returns true if this enode has no children.
    fn is_leaf(&self) -> bool {
        self.all(|_| false)
    }

    /// Runs a given function to replace the children.
    fn update_children<F: FnMut(Id) -> Id>(&mut self, mut f: F) {
        self.for_each_mut(|id| *id = f(*id))
    }

    /// Creates a new enode with children determined by the given function.
    fn map_children<F: FnMut(Id) -> Id>(mut self, f: F) -> Self {
        self.update_children(f);
        self
    }

    /// Folds over the children, given an initial accumulator.
    fn fold<F, T>(&self, init: T, mut f: F) -> T
    where
        F: FnMut(T, Id) -> T,
    {
        let mut acc = init;
        for id in self.children().iter().copied() {
            acc = f(acc, id)
        }
        acc
    }

    /// Returns true if the predicate is true on all children.
    /// Does not short circuit.
    fn all<F: FnMut(Id) -> bool>(&self, mut f: F) -> bool {
        self.fold(true, |acc, id| acc && f(id))
    }

    /// Returns true if the predicate is true on any children.
    /// Does not short circuit.
    fn any<F: FnMut(Id) -> bool>(&self, mut f: F) -> bool {
        self.fold(false, |acc, id| acc || f(id))
    }

    /// Make a [`RecExpr`] by mapping this enodes children to other [`RecExpr`]s.
    ///
    /// This can be used to join together different expression with a new node.
    ///
    /// # Example
    /// ```
    /// # use egg::*;
    /// let a_plus_2: RecExpr<SymbolLang> = "(+ a 2)".parse().unwrap();
    /// // here's an enode with some meaningless child ids
    /// let enode = SymbolLang::new("*", vec![Id::from(0), Id::from(0)]);
    /// // make a new recexpr, replacing enode's children with a_plus_2
    /// let recexpr = enode.join_recexprs(|_id| &a_plus_2);
    /// assert_eq!(recexpr, "(* (+ a 2) (+ a 2))".parse().unwrap())
    /// ```
    fn join_recexprs<F, Expr>(&self, mut child_recexpr: F) -> RecExpr<Self>
    where
        F: FnMut(Id) -> Expr,
        Expr: AsRef<[Self]>,
    {
        fn build<L: Language>(to: &mut RecExpr<L>, from: &[L]) -> Id {
            let last = from.last().unwrap().clone();
            let new_node = last.map_children(|id| {
                let i = usize::from(id) + 1;
                build(to, &from[0..i])
            });
            to.add(new_node)
        }

        let mut expr = RecExpr::default();
        let node = self
            .clone()
            .map_children(|id| build(&mut expr, child_recexpr(id).as_ref()));
        expr.add(node);
        expr
    }

    /// Build a [`RecExpr`] from an e-node.
    ///
    /// The provided `get_node` function must return the same node for a given
    /// [`Id`] on multiple invocations.
    ///
    /// # Example
    ///
    /// You could use this method to perform an "ad-hoc" extraction from the e-graph,
    /// where you already know which node you want pick for each class:
    /// ```
    /// # use egg::*;
    /// let mut egraph = EGraph::<SymbolLang, ()>::default();
    /// let expr = "(foo (bar1 (bar2 (bar3 baz))))".parse().unwrap();
    /// let root = egraph.add_expr(&expr);
    /// let get_first_enode = |id| egraph[id].nodes[0].clone();
    /// let expr2 = get_first_enode(root).build_recexpr(get_first_enode);
    /// assert_eq!(expr, expr2)
    /// ```
    fn build_recexpr<F>(&self, mut get_node: F) -> RecExpr<Self>
    where
        F: FnMut(Id) -> Self,
    {
        self.try_build_recexpr::<_, std::convert::Infallible>(|id| Ok(get_node(id)))
            .unwrap()
    }

    /// Same as [`Language::build_recexpr`], but fallible.
    fn try_build_recexpr<F, Err>(&self, mut get_node: F) -> Result<RecExpr<Self>, Err>
    where
        F: FnMut(Id) -> Result<Self, Err>,
    {
        let mut set = IndexSet::<Self>::default();
        let mut ids = HashMap::<Id, Id>::default();
        let mut todo = self.children().to_vec();

        while let Some(id) = todo.last().copied() {
            if ids.contains_key(&id) {
                todo.pop();
                continue;
            }

            let node = get_node(id)?;

            // check to see if we can do this node yet
            let mut ids_has_all_children = true;
            for child in node.children() {
                if !ids.contains_key(child) {
                    ids_has_all_children = false;
                    todo.push(*child)
                }
            }

            // all children are processed, so we can lookup this node safely
            if ids_has_all_children {
                let node = node.map_children(|id| ids[&id]);
                let new_id = set.insert_full(node).0;
                ids.insert(id, Id::from(new_id));
                todo.pop();
            }
        }

        // finally, create the expression and add the root node
        let mut expr: RecExpr<_> = set.into_iter().collect();
        expr.add(self.clone().map_children(|id| ids[&id]));
        Ok(expr)
    }
}

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

/// A recursive expression from a user-defined [`Language`].
///
/// This conceptually represents a recursive expression, but it's actually just
/// a list of enodes.
///
/// [`RecExpr`]s must satisfy the invariant that enodes' children must refer to
/// elements that come before it in the list. For example, the expression
/// `(+ (* x 5) x)` could be represented by a recursive expression of the form
/// `[Num(5), Var("x"), Mul(1, 0), Add(2, 1)]`.
///
/// If the `serde-1` feature is enabled, this implements
/// [`serde::Serialize`](https://docs.rs/serde/latest/serde/trait.Serialize.html).
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct RecExpr<L> {
    nodes: Vec<L>,
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

impl<L> Default for RecExpr<L> {
    fn default() -> Self {
        Self::from(vec![])
    }
}

impl<L> Borrow<[L]> for RecExpr<L> {
    fn borrow(&self) -> &[L] {
        &self.nodes
    }
}

impl<L> BorrowMut<[L]> for RecExpr<L> {
    fn borrow_mut(&mut self) -> &mut [L] {
        &mut self.nodes
    }
}

impl<L> Deref for RecExpr<L> {
    type Target = [L];

    fn deref(&self) -> &Self::Target {
        self.borrow()
    }
}

impl<L> DerefMut for RecExpr<L> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.borrow_mut()
    }
}

impl<L> AsRef<[L]> for RecExpr<L> {
    fn as_ref(&self) -> &[L] {
        &self.nodes
    }
}

impl<L> AsMut<[L]> for RecExpr<L> {
    fn as_mut(&mut self) -> &mut [L] {
        &mut self.nodes
    }
}

impl<L> From<Vec<L>> for RecExpr<L> {
    fn from(nodes: Vec<L>) -> Self {
        Self { nodes }
    }
}

impl<L> From<RecExpr<L>> for Vec<L> {
    fn from(val: RecExpr<L>) -> Self {
        val.nodes
    }
}

impl<L> FromIterator<L> for RecExpr<L> {
    fn from_iter<T: IntoIterator<Item = L>>(iter: T) -> Self {
        Self::from(iter.into_iter().collect::<Vec<_>>())
    }
}

impl<L: Language> RecExpr<L> {
    /// Adds a given enode to this `RecExpr`.
    /// The enode's children [`Id`]s must refer to elements already in this list.
    pub fn add(&mut self, node: L) -> Id {
        debug_assert!(
            node.all(|id| id <= self.root()),
            "node {:?} has children not in this expr: {:?}",
            node,
            self
        );
        self.nodes.push(node);
        self.root()
    }

    pub(crate) fn compact(mut self) -> Self {
        let mut ids = hashmap_with_capacity::<Id, Id>(self.len());
        let mut set = IndexSet::default();
        for (i, node) in self.nodes.drain(..).enumerate() {
            let node = node.map_children(|id| ids[&id]);
            let new_id = set.insert_full(node).0;
            ids.insert(Id::from(i), Id::from(new_id));
        }
        self.nodes.extend(set);
        self
    }

    pub(crate) fn extract(&self, new_root: Id) -> Self {
        self[new_root].build_recexpr(|id| self[id].clone())
    }

    /// Returns an iterator over the [`Id`]s in this expression.
    pub fn ids(&self) -> impl ExactSizeIterator<Item = Id> + DoubleEndedIterator {
        (0..self.len()).map(Id::from)
    }

    /// Returns an iterator over the [`Id`]s and enodes of this expression.
    pub fn items(&self) -> impl ExactSizeIterator<Item = (Id, &L)> + DoubleEndedIterator {
        self.ids().zip(self)
    }

    /// Returns an iterator over the [`Id`]s and enodes of this expression.
    pub fn items_mut(
        &mut self,
    ) -> impl ExactSizeIterator<Item = (Id, &mut L)> + DoubleEndedIterator {
        self.ids().zip(self)
    }

    /// Checks if this expr is a DAG, i.e. doesn't have any back edges
    pub fn is_dag(&self) -> bool {
        self.items().all(|(id, n)| n.all(|child| child < id))
    }

    /// Get the root node of this expression. When adding a new node via `add`, it becomes the new root.
    pub fn root(&self) -> Id {
        self.ids().last().unwrap()
    }
}

impl<L: Language> Index<Id> for RecExpr<L> {
    type Output = L;
    fn index(&self, id: Id) -> &L {
        &self.nodes[usize::from(id)]
    }
}

impl<L: Language> IndexMut<Id> for RecExpr<L> {
    fn index_mut(&mut self, id: Id) -> &mut L {
        &mut self.nodes[usize::from(id)]
    }
}

impl<L> IntoIterator for RecExpr<L> {
    type Item = L;
    type IntoIter = std::vec::IntoIter<L>;

    fn into_iter(self) -> Self::IntoIter {
        self.nodes.into_iter()
    }
}

impl<'a, L> IntoIterator for &'a RecExpr<L> {
    type Item = &'a L;
    type IntoIter = std::slice::Iter<'a, L>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a, L> IntoIterator for &'a mut RecExpr<L> {
    type Item = &'a mut L;
    type IntoIter = std::slice::IterMut<'a, L>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
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

    fn make(egraph: &mut EGraph<SimpleMath, Self>, enode: &SimpleMath, _id: Id) -> Self::Data {
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
    type Data: Debug;

    /// Makes a new [`Analysis`] data for a given e-node that will go into the given e-class.
    ///
    /// Note the mutable `egraph` parameter: this is needed for some
    /// advanced use cases, but most use cases will not need to mutate
    /// the e-graph in any way.
    /// It is **not** `make`'s responsiblity to insert the e-node;
    /// the e-node is "being inserted" when this function is called.
    /// Doing so will create an infinite loop.
    ///
    /// Note that `enode`'s children may not be canonical
    fn make(egraph: &mut EGraph<L, Self>, enode: &L, id: Id) -> Self::Data;

    /// Same as [`Analysis::make`], but called during rebuilding.
    ///
    /// By default, it just calls `make`.
    fn remake(egraph: &mut EGraph<L, Self>, enode: &L, id: Id) -> Self::Data {
        Self::make(egraph, enode, id)
    }

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

    /// Whether or not e-matching should allow finding cycles.
    ///
    /// By default, this returns `true`.
    ///
    /// Setting this to `false` can improve performance in some cases, but risks
    /// missing some equalities depending on the use case.
    fn allow_ematching_cycles(&self) -> bool {
        true
    }
}

impl<L: Language> Analysis<L> for () {
    type Data = ();
    fn make(_egraph: &mut EGraph<L, Self>, _enode: &L, _id: Id) -> Self::Data {}
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
