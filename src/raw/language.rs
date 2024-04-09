use crate::Id;
use std::fmt::Debug;
use std::hash::Hash;
use std::ops::{Index, IndexMut};

/// A recursive expression from a user-defined [`Language`].
///
/// This conceptually represents a recursive expression, but it's actually just
/// a list of enodes.
///
/// [`RecExpr`]s must satisfy the invariant that enodes' children must refer to
/// elements that come before it in the list.
///
/// If the `serde-1` feature is enabled, this implements
/// [`serde::Serialize`](https://docs.rs/serde/latest/serde/trait.Serialize.html).
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct RecExpr<L> {
    pub(crate) nodes: Vec<L>,
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

impl<L> From<RecExpr<L>> for Vec<L> {
    fn from(val: RecExpr<L>) -> Self {
        val.nodes
    }
}

impl<L: Language> RecExpr<L> {
    /// Adds a given enode to this `RecExpr`.
    /// The enode's children `Id`s must refer to elements already in this list.
    pub fn add(&mut self, node: L) -> Id {
        debug_assert!(
            node.all(|id| usize::from(id) < self.nodes.len()),
            "node {:?} has children not in this expr: {:?}",
            node,
            self
        );
        self.nodes.push(node);
        Id::from(self.nodes.len() - 1)
    }

    /// Checks if this expr is a DAG, i.e. doesn't have any back edges
    pub fn is_dag(&self) -> bool {
        for (i, n) in self.nodes.iter().enumerate() {
            for &child in n.children() {
                if usize::from(child) >= i {
                    return false;
                }
            }
        }
        true
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
    /// This should only consider the operator, not the children `Id`s.
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
        E: Clone,
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
        T: Clone,
    {
        let mut acc = init;
        self.for_each(|id| acc = f(acc.clone(), id));
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

    #[cfg(feature = "egg_compat")]

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

    #[cfg(feature = "egg_compat")]
    /// Same as [`Language::build_recexpr`], but fallible.
    fn try_build_recexpr<F, Err>(&self, mut get_node: F) -> Result<RecExpr<Self>, Err>
    where
        F: FnMut(Id) -> Result<Self, Err>,
    {
        use crate::util::*;
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

        // finally, add the root node and create the expression
        let mut nodes: Vec<Self> = set.into_iter().collect();
        nodes.push(self.clone().map_children(|id| ids[&id]));
        Ok(RecExpr::from(nodes))
    }
}
