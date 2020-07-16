use std::convert::TryFrom;
use std::fmt::{self, Debug, Display};
use std::hash::Hash;

use crate::{EGraph, Id, Symbol};

use symbolic_expressions::Sexp;

/// Trait that defines a Language whose terms will be in the [`EGraph`].
///
/// Check out the [`define_language!`] macro for an easy way to create
/// a [`Language`].
///
/// Note that the default implementations of
/// [`from_op_str`](trait.Language.html#method.from_op_str) and
/// [`display_op`](trait.Language.html#method.display_op) panic. You
/// should override them if you want to parse or pretty-print expressions.
/// [`define_language!`] implements these for you.
///
/// See [`SymbolLang`](struct.SymbolLang.html) for quick-and-dirty use cases.
///
/// [`define_language!`]: macro.define_language.html
/// [`Language`]: trait.Language.html
/// [`EGraph`]: struct.EGraph.html
/// [`FromStr`]: https://doc.rust-lang.org/std/str/trait.FromStr.html
/// [`Display`]: https://doc.rust-lang.org/std/fmt/trait.Display.html
#[allow(clippy::len_without_is_empty)]
pub trait Language: Debug + Clone + Eq + Ord + Hash {
    /// Returns true if this enode matches another enode.
    /// This should only consider the operator, not the children `Id`s.
    fn matches(&self, other: &Self) -> bool;

    /// Return a slice of the children `Id`s.
    fn children(&self) -> &[Id];

    /// Return a mutable slice of the children `Id`s.
    fn children_mut(&mut self) -> &mut [Id];

    /// Runs a given function on each child `Id`.
    fn for_each<F: FnMut(Id)>(&self, f: F) {
        self.children().iter().copied().for_each(f)
    }

    /// Runs a given function on each child `Id`, allowing mutation of that `Id`.
    fn for_each_mut<F: FnMut(&mut Id)>(&mut self, f: F) {
        self.children_mut().iter_mut().for_each(f)
    }

    /// Returns something that will print the operator.
    ///
    /// Default implementation panics, so make sure to implement this if you
    /// want to print `Language` elements.
    /// The [`define_language!`](macro.define_language.html) macro will
    /// implement this for you.
    fn display_op(&self) -> &dyn Display {
        unimplemented!("display_op not implemented")
    }

    /// Given a string for the operator and the children, tries to make an
    /// enode.
    ///
    /// Default implementation panics, so make sure to implement this if you
    /// want to parse `Language` elements.
    /// The [`define_language!`](macro.define_language.html) macro will
    /// implement this for you.
    #[allow(unused_variables)]
    fn from_op_str(op_str: &str, children: Vec<Id>) -> Result<Self, String> {
        unimplemented!("from_op_str not implemented")
    }

    /// Returns the number of the children this enode has.
    ///
    /// The default implementation uses `fold` to accumulate the number of
    /// children.
    fn len(&self) -> usize {
        self.children().len()
    }

    /// Returns true if this enode has no children.
    fn is_leaf(&self) -> bool {
        self.children().is_empty()
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
        T: Clone,
    {
        let mut acc = init;
        self.for_each(|id| acc = f(acc.clone(), id));
        acc
    }

    /// Make a `RecExpr` converting this enodes children to `RecExpr`s
    ///
    /// # Example
    /// ```
    /// # use egg::*;
    /// let a_plus_2: RecExpr<SymbolLang> = "(+ a 2)".parse().unwrap();
    /// // here's an enode with some meaningless child ids
    /// let enode = SymbolLang::new("*", vec![Id::from(0), Id::from(0)]);
    /// // make a new recexpr, replacing enode's childen with a_plus_2
    /// let recexpr = enode.to_recexpr(|_id| a_plus_2.as_ref());
    /// assert_eq!(recexpr, "(* (+ a 2) (+ a 2))".parse().unwrap())
    /// ```
    fn to_recexpr<'a, F>(&self, mut child_recexpr: F) -> RecExpr<Self>
    where
        Self: 'a,
        F: FnMut(Id) -> &'a [Self],
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
            .map_children(|id| build(&mut expr, child_recexpr(id)));
        expr.add(node);
        expr
    }
}

/// A marker that defines acceptable children types for [`define_language!`].
///
/// See [`define_language!`] for more details.
/// You should not have to implement this trait.
///
/// [`define_language!`]: macro.define_language.html
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

macro_rules! impl_array {
    () => {};
    ($n:literal, $($rest:tt)*) => {
        impl LanguageChildren for [Id; $n] {
            fn len(&self) -> usize                   { <[Id]>::len(self) }
            fn can_be_length(n: usize) -> bool       { n == $n }
            fn from_vec(v: Vec<Id>) -> Self          { Self::try_from(v.as_slice()).unwrap() }
            fn as_slice(&self) -> &[Id]              { self }
            fn as_mut_slice(&mut self) -> &mut [Id]  { self }
        }
        impl_array!($($rest)*);
    };
}

impl_array!(0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,);

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
/// elements that come before it in the list.
///
/// If the `serde-1` feature is enabled, this implements
/// [`serde::Serialize`][ser].
///
/// [`RecExpr`]: struct.RecExpr.html
/// [`Language`]: trait.Language.html
/// [ser]: https://docs.rs/serde/latest/serde/trait.Serialize.html
/// [pretty]: struct.RecExpr.html#method.pretty
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct RecExpr<L> {
    nodes: Vec<L>,
}

#[cfg(feature = "serde-1")]
impl<L: Language> serde::Serialize for RecExpr<L> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        let s = self.to_sexp(self.nodes.len() - 1).to_string();
        serializer.serialize_str(&s)
    }
}

impl<L> Default for RecExpr<L> {
    fn default() -> Self {
        Self::from(vec![])
    }
}

impl<L> AsRef<[L]> for RecExpr<L> {
    fn as_ref(&self) -> &[L] {
        &self.nodes
    }
}

impl<L> From<Vec<L>> for RecExpr<L> {
    fn from(nodes: Vec<L>) -> Self {
        Self { nodes }
    }
}

impl<L: Language> RecExpr<L> {
    /// Adds a given enode to this `RecExpr`.
    /// The enode's children `Id`s must refer to elements already in this list.
    pub fn add(&mut self, node: L) -> Id {
        debug_assert!(
            node.children()
                .iter()
                .all(|&id| usize::from(id) < self.nodes.len()),
            "node {:?} has children not in this expr: {:?}",
            node,
            self
        );
        self.nodes.push(node);
        Id::from(self.nodes.len() - 1)
    }
}

impl<L: Language> Display for RecExpr<L> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.nodes.is_empty() {
            write!(f, "()")
        } else {
            let s = self.to_sexp(self.nodes.len() - 1).to_string();
            write!(f, "{}", s)
        }
    }
}

impl<L: Language> RecExpr<L> {
    fn to_sexp(&self, i: usize) -> Sexp {
        let node = &self.nodes[i];
        let op = Sexp::String(node.display_op().to_string());
        if node.is_leaf() {
            op
        } else {
            let mut vec = vec![op];
            node.for_each(|id| vec.push(self.to_sexp(id.into())));
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
        use std::fmt::{Result, Write};
        let sexp = self.to_sexp(self.nodes.len() - 1);

        fn pp(buf: &mut String, sexp: &Sexp, width: usize, level: usize) -> Result {
            if let Sexp::List(list) = sexp {
                let indent = sexp.to_string().len() > width;
                write!(buf, "(")?;

                for (i, val) in list.iter().enumerate() {
                    if indent && i > 0 {
                        writeln!(buf)?;
                        for _ in 0..level {
                            write!(buf, "  ")?;
                        }
                    }
                    pp(buf, val, width, level + 1)?;
                    if !indent && i < list.len() - 1 {
                        write!(buf, " ")?;
                    }
                }

                write!(buf, ")")?;
                Ok(())
            } else {
                // I don't care about quotes
                write!(buf, "{}", sexp.to_string().trim_matches('"'))
            }
        }

        let mut buf = String::new();
        pp(&mut buf, &sexp, width, 1).unwrap();
        buf
    }
}

macro_rules! bail {
    ($s:literal $(,)?) => {
        return Err($s.into())
    };
    ($s:literal, $($args:expr),+) => {
        return Err(format!($s, $($args),+).into())
    };
}

impl<L: Language> std::str::FromStr for RecExpr<L> {
    type Err = String;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        fn parse_sexp_into<L: Language>(sexp: &Sexp, expr: &mut RecExpr<L>) -> Result<Id, String> {
            match sexp {
                Sexp::Empty => Err("Found empty s-expression".into()),
                Sexp::String(s) => {
                    let node = L::from_op_str(s, vec![])?;
                    Ok(expr.add(node))
                }
                Sexp::List(list) if list.is_empty() => Err("Found empty s-expression".into()),
                Sexp::List(list) => match &list[0] {
                    Sexp::Empty => unreachable!("Cannot be in head position"),
                    Sexp::List(l) => bail!("Found a list in the head position: {:?}", l),
                    Sexp::String(op) => {
                        let arg_ids: Result<Vec<Id>, _> =
                            list[1..].iter().map(|s| parse_sexp_into(s, expr)).collect();

                        let node = L::from_op_str(op, arg_ids?).map_err(|e| {
                            format!("Failed to parse '{}', error message:\n{}", sexp, e)
                        })?;
                        Ok(expr.add(node))
                    }
                },
            }
        }

        let mut expr = RecExpr::default();
        let sexp = symbolic_expressions::parser::parse_str(s.trim()).map_err(|e| e.to_string())?;
        parse_sexp_into(&sexp, &mut expr)?;
        Ok(expr)
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

// in this case, our analysis itself doens't require any data, so we can just
// use a unit struct and derive Default
#[derive(Default)]
struct ConstantFolding;
impl Analysis<SimpleMath> for ConstantFolding {
    type Data = Option<i32>;

    fn merge(&self, to: &mut Self::Data, from: Self::Data) -> bool {
        egg::merge_if_different(to, to.or(from))
    }

    fn make(egraph: &EGraph<SimpleMath, Self>, enode: &SimpleMath) -> Self::Data {
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

[`Analysis`]: trait.Analysis.html
[`EClass`]: struct.EClass.html
[`ENode`]: struct.ENode.html
[`math.rs`]: https://github.com/mwillsey/egg/blob/master/tests/math.rs
[`prop.rs`]: https://github.com/mwillsey/egg/blob/master/tests/prop.rs
*/

pub trait Analysis<L: Language>: Sized {
    /// The per-[`EClass`](struct.EClass.html) data for this analysis.
    type Data: Debug;

    /// Makes a new [`Analysis`] for a given enode
    /// [`Analysis`].
    ///
    /// [`Analysis`]: trait.Analysis.html
    fn make(egraph: &EGraph<L, Self>, enode: &L) -> Self::Data;

    /// Defines how to merge two `Data`s when their containing
    /// [`EClass`]es merge.
    ///
    /// [`EClass`]: struct.EClass.html
    fn merge(&self, to: &mut Self::Data, from: Self::Data) -> bool;

    /// A hook that allows the modification of the
    /// [`EGraph`](struct.EGraph.html)
    ///
    /// By default this does nothing.
    #[allow(unused_variables)]
    fn modify(egraph: &mut EGraph<L, Self>, id: Id) {}
}

/// Replace the first with second value if they are different returning whether
/// or not something was done.
///
/// Useful for implementing
/// [`Analysis::merge`](trait.Analysis.html#tymethod.merge).
///
/// ```
/// # use egg::*;
/// let mut x = 6;
/// assert!(!merge_if_different(&mut x, 6));
/// assert!(merge_if_different(&mut x, 7));
/// assert_eq!(x, 7);
/// ```
pub fn merge_if_different<D: PartialEq>(to: &mut D, new: D) -> bool {
    if *to == new {
        false
    } else {
        *to = new;
        true
    }
}

impl<L: Language> Analysis<L> for () {
    type Data = ();
    fn make(_egraph: &EGraph<L, Self>, _enode: &L) -> Self::Data {}
    fn merge(&self, _to: &mut Self::Data, _from: Self::Data) -> bool {
        false
    }
}

/// A simple language used for testing.
#[derive(Debug, Hash, PartialEq, Eq, Clone, PartialOrd, Ord)]
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
    fn matches(&self, other: &Self) -> bool {
        self.op == other.op && self.len() == other.len()
    }

    fn children(&self) -> &[Id] {
        &self.children
    }

    fn children_mut(&mut self) -> &mut [Id] {
        &mut self.children
    }

    fn display_op(&self) -> &dyn Display {
        &self.op
    }

    fn from_op_str(op_str: &str, children: Vec<Id>) -> Result<Self, String> {
        Ok(Self {
            op: op_str.into(),
            children,
        })
    }
}
