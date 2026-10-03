import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Logic.Relation
import Mathlib.Tactic.Linarith

/-!
An abstract proof of the rank constraints proposed for egg's LP extractor.

`edge parent child` means that a selected e-node of `parent` contains `child`.
All classes are canonical and form a finite type. Acyclicity excludes every
nonempty directed closed walk, represented by `Relation.TransGen`.

This file proves facts about exact mathematical reals and Boolean selections.
It does not verify Rust, good_lp, any numerical solver, or expression assembly.
-/

namespace EggLpRank

open Relation

variable {Class : Type*} [Fintype Class]

/-- No nonempty selected-edge path returns to its starting class. -/
def Acyclic (edge : Class → Class → Prop) : Prop :=
  ∀ v, ¬ TransGen edge v v

/-- Exact real ranks used by the proposed LP constraints. -/
def BoundedRank (rank : Class → ℝ) : Prop :=
  ∀ v, 0 ≤ rank v ∧ rank v ≤ (Fintype.card Class : ℝ) - 1

noncomputable def descendants (edge : Class → Class → Prop) (v : Class) : Finset Class := by
  classical
  exact Finset.univ.filter (TransGen edge v)

@[simp] theorem mem_descendants (edge : Class → Class → Prop) (v w : Class) :
    w ∈ descendants edge v ↔ TransGen edge v w := by
  classical
  simp [descendants]

/-- An edge strictly increases the number of reachable descendants. -/
theorem descendants_strict (edge : Class → Class → Prop) (hacyc : Acyclic edge)
    {parent child : Class} (h : edge parent child) :
    descendants edge child ⊂ descendants edge parent := by
  classical
  have hsub : descendants edge child ⊆ descendants edge parent := by
    intro v hv
    exact (mem_descendants edge parent v).mpr
      ((mem_descendants edge child v).mp hv |>.head h)
  apply (Finset.ssubset_iff_of_subset hsub).mpr
  refine ⟨child, ?_, ?_⟩
  · exact (mem_descendants edge parent child).mpr (.single h)
  · simpa only [mem_descendants] using hacyc child

/-- Every class excludes itself from its descendants in an acyclic graph. -/
theorem descendants_card_lt (edge : Class → Class → Prop) (hacyc : Acyclic edge)
    (v : Class) : (descendants edge v).card < Fintype.card Class := by
  classical
  have hsub : descendants edge v ⊆ (Finset.univ : Finset Class) := Finset.subset_univ _
  have hstrict : descendants edge v ⊂ (Finset.univ : Finset Class) := by
    apply (Finset.ssubset_iff_of_subset hsub).mpr
    exact ⟨v, Finset.mem_univ v, by simpa only [mem_descendants] using hacyc v⟩
  simpa using Finset.card_lt_card hstrict

/-- Every finite DAG has exact bounded ranks with a gap of at least one. -/
theorem bounded_rank_exists (edge : Class → Class → Prop) (hacyc : Acyclic edge) :
    ∃ rank : Class → ℝ, BoundedRank rank ∧
      ∀ parent child, edge parent child → rank child + 1 ≤ rank parent := by
  classical
  let rank : Class → ℝ := fun v => ((descendants edge v).card : ℝ)
  refine ⟨rank, ?_, ?_⟩
  · intro v
    constructor
    · exact Nat.cast_nonneg _
    · have hn := descendants_card_lt edge hacyc v
      have hn' : (descendants edge v).card + 1 ≤ Fintype.card Class := hn
      have hr : ((descendants edge v).card : ℝ) + 1 ≤ (Fintype.card Class : ℝ) := by
        exact_mod_cast hn'
      dsimp [rank]
      linarith
  · intro parent child h
    have hn : (descendants edge child).card + 1 ≤ (descendants edge parent).card :=
      Finset.card_lt_card (descendants_strict edge hacyc h)
    dsimp [rank]
    exact_mod_cast hn

omit [Fintype Class] in
/-- Strictly decreasing ranks prohibit every nonempty selected-edge cycle. -/
theorem rank_sound (edge : Class → Class → Prop) (rank : Class → ℝ)
    (hedge : ∀ parent child, edge parent child → rank child + 1 ≤ rank parent) :
    Acyclic edge := by
  have hpath : ∀ {parent child}, TransGen edge parent child → rank child < rank parent := by
    intro parent child h
    induction h with
    | single h => have := hedge _ _ h; linarith
    | tail _ h ih => have := hedge _ _ h; linarith
  intro v hv
  exact (lt_irrefl (rank v)) (hpath hv)

/-- The selected relation is acyclic exactly when bounded real ranks exist. -/
theorem acyclic_iff_bounded_rank (edge : Class → Class → Prop) :
    Acyclic edge ↔ ∃ rank : Class → ℝ, BoundedRank rank ∧
      ∀ parent child, edge parent child → rank child + 1 ≤ rank parent := by
  constructor
  · exact bounded_rank_exists edge
  · rintro ⟨rank, _, hedge⟩
    exact rank_sound edge rank hedge

/-- The exact real value of a binary e-node selection variable. -/
def bit (selected : Bool) : ℝ := if selected then 1 else 0

/-- With bounded ranks, M = n makes an unselected edge constraint redundant. -/
theorem conditional_iff (rank : Class → ℝ) (hbound : BoundedRank rank)
    (parent child : Class) (selected : Bool) :
    rank child + 1 - (Fintype.card Class : ℝ) * (1 - bit selected) ≤ rank parent ↔
      (selected = true → rank child + 1 ≤ rank parent) := by
  cases selected
  · simp only [bit, Bool.false_eq_true, if_false, sub_zero, mul_one, false_implies,
      iff_true]
    have hp := (hbound parent).1
    have hc := (hbound child).2
    linarith
  · simp [bit]

variable {Node : Type*}

/-- Selected edges allow arbitrary child predicates, including sharing and repeats. -/
def SelectedEdge (owner : Node → Class) (children : Node → Class → Prop)
    (selected : Node → Bool) (parent child : Class) : Prop :=
  ∃ node, selected node = true ∧ owner node = parent ∧ children node child

/-- One conditional rank inequality for each possible e-node child occurrence. -/
def ConditionalConstraints (owner : Node → Class) (children : Node → Class → Prop)
    (selected : Node → Bool) (rank : Class → ℝ) : Prop :=
  ∀ node child, children node child →
    rank child + 1 - (Fintype.card Class : ℝ) * (1 - bit (selected node)) ≤ rank (owner node)

theorem constraints_iff_selected_edges (owner : Node → Class)
    (children : Node → Class → Prop) (selected : Node → Bool) (rank : Class → ℝ)
    (hbound : BoundedRank rank) :
    ConditionalConstraints owner children selected rank ↔
      ∀ parent child, SelectedEdge owner children selected parent child →
        rank child + 1 ≤ rank parent := by
  constructor
  · intro h parent child hedge
    rcases hedge with ⟨node, hselected, rfl, hchild⟩
    exact (conditional_iff rank hbound (owner node) child (selected node)).mp
      (h node child hchild) hselected
  · intro h node child hchild
    apply (conditional_iff rank hbound (owner node) child (selected node)).mpr
    intro hselected
    exact h (owner node) child ⟨node, hselected, rfl, hchild⟩

/-- Main theorem: the proposed rank part preserves every DAG selection and only those. -/
theorem encoding_sound_and_complete (owner : Node → Class)
    (children : Node → Class → Prop) (selected : Node → Bool) :
    Acyclic (SelectedEdge owner children selected) ↔
      ∃ rank : Class → ℝ, BoundedRank rank ∧
        ConditionalConstraints owner children selected rank := by
  rw [acyclic_iff_bounded_rank]
  constructor
  · rintro ⟨rank, hbound, hedge⟩
    exact ⟨rank, hbound,
      (constraints_iff_selected_edges owner children selected rank hbound).mpr hedge⟩
  · rintro ⟨rank, hbound, hconstraints⟩
    exact ⟨rank, hbound,
      (constraints_iff_selected_edges owner children selected rank hbound).mp hconstraints⟩

omit [Fintype Class] in
/-- A direct self-loop can safely be forbidden before model construction. -/
theorem selected_self_loop_impossible (owner : Node → Class)
    (children : Node → Class → Prop) (selected : Node → Bool)
    (hacyc : Acyclic (SelectedEdge owner children selected))
    (node : Node) (hself : children node (owner node)) : selected node ≠ true := by
  intro hselected
  apply hacyc (owner node)
  exact .single ⟨node, hselected, rfl, hself⟩

section Components

variable {Label : Type*}

/-- Sufficient partition property: every possible edge on a closed nonempty
walk stays in one component. Components may conservatively merge exact SCCs. -/
def CyclePartition (possible : Class → Class → Prop) (component : Class → Label) : Prop :=
  ∀ a b, possible a b → TransGen possible b a → component a = component b

/-- Exact SCC labels identify precisely the mutually reachable classes.
Reflexive reachability includes singleton components with no self-loop. -/
def ExactSCCPartition (possible : Class → Class → Prop)
    (component : Class → Label) : Prop :=
  ∀ a b, component a = component b ↔
    ReflTransGen possible a b ∧ ReflTransGen possible b a

omit [Fintype Class] in
theorem exact_scc_partition_is_cycle_partition (possible : Class → Class → Prop)
    (component : Class → Label) (h : ExactSCCPartition possible component) :
    CyclePartition possible component := by
  intro a b hab hba
  exact (h a b).mpr ⟨.single hab, hba.to_reflTransGen⟩

/-- Only selected edges whose endpoints have equal component labels. -/
def InternalEdge (edge : Class → Class → Prop) (component : Class → Label)
    (a b : Class) : Prop := edge a b ∧ component a = component b

omit [Fintype Class] in
/-- Every edge on a selected closed walk stays in its possible-edge component. -/
theorem returning_path_internal (possible edge : Class → Class → Prop)
    (component : Class → Label) (hsub : ∀ a b, edge a b → possible a b)
    (hpart : CyclePartition possible component) {a b : Class}
    (hab : TransGen edge a b) (hba : TransGen edge b a) :
    TransGen (InternalEdge edge component) a b := by
  revert hba
  induction hab with
  | single hab =>
      intro hba
      exact .single ⟨hab, hpart _ _ (hsub _ _ hab) (hba.mono hsub)⟩
  | @tail b c hab hbc ih =>
      intro hba
      have hcb : TransGen edge c b := hba.trans hab
      exact (ih (hba.head hbc)).tail
        ⟨hbc, hpart _ _ (hsub _ _ hbc) (hcb.mono hsub)⟩

omit [Fintype Class] in
/-- Cross-component rows are unnecessary for cycle exclusion. -/
theorem acyclic_iff_internal (possible edge : Class → Class → Prop)
    (component : Class → Label) (hsub : ∀ a b, edge a b → possible a b)
    (hpart : CyclePartition possible component) :
    Acyclic edge ↔ Acyclic (InternalEdge edge component) := by
  constructor
  · intro h v hv
    exact h v (hv.mono fun _ _ hedge => hedge.1)
  · intro h v hv
    exact h v (returning_path_internal possible edge component hsub hpart hv hv)

/-- The finite subtype of classes with a given component label. -/
abbrev Component (component : Class → Label) (label : Label) :=
  {v : Class // component v = label}

/-- Restriction of an edge relation to one finite component subtype. -/
def ComponentEdge (edge : Class → Class → Prop) (component : Class → Label)
    (label : Label) (a b : Component component label) : Prop := edge a.val b.val

omit [Fintype Class] in
theorem internal_path_in_component (edge : Class → Class → Prop)
    (component : Class → Label) (label : Label) {a b : Class}
    (hab : TransGen (InternalEdge edge component) a b) :
    ∀ (ha : component a = label) (hb : component b = label),
      TransGen (ComponentEdge edge component label) ⟨a, ha⟩ ⟨b, hb⟩ := by
  induction hab with
  | single hab =>
      intro ha hb
      exact .single hab.1
  | @tail b c hab hbc ih =>
      intro ha hc
      exact (ih ha (hbc.2.trans hc)).tail hbc.1

omit [Fintype Class] in
/-- Acyclicity can be checked independently on every component subtype. -/
theorem acyclic_iff_components (possible edge : Class → Class → Prop)
    (component : Class → Label) (hsub : ∀ a b, edge a b → possible a b)
    (hpart : CyclePartition possible component) :
    Acyclic edge ↔ ∀ label, Acyclic (ComponentEdge edge component label) := by
  constructor
  · intro h label v hv
    exact h v.val (hv.lift Subtype.val fun _ _ hedge => hedge)
  · intro h
    apply (acyclic_iff_internal possible edge component hsub hpart).mpr
    intro v hv
    exact h (component v) ⟨v, rfl⟩
      (internal_path_in_component edge component (component v) hv rfl rfl)

variable [DecidableEq Label]

/-- Exactly the rank-variable domain: fibers of size at least two.
Empty and singleton fibers require no rank function. -/
abbrev SCCRanks (component : Class → Label) :=
  (label : Label) → (1 < Fintype.card (Component component label)) →
    Component component label → ℝ

/-- All possible e-node-child edges, regardless of the chosen alternatives. -/
def PossibleEdge (owner : Node → Class) (children : Node → Class → Prop)
    (parent child : Class) : Prop :=
  ∃ node, owner node = parent ∧ children node child

omit [Fintype Class] [DecidableEq Label] in
theorem selected_subrelation_possible (owner : Node → Class)
    (children : Node → Class → Prop) (selected : Node → Bool) :
    ∀ a b, SelectedEdge owner children selected a b → PossibleEdge owner children a b := by
  rintro a b ⟨node, _, howner, hchild⟩
  exact ⟨node, howner, hchild⟩

/-- The binary upper bound zero imposed on every directly self-looping e-node. -/
def SelfLoopsDisabled (owner : Node → Class) (children : Node → Class → Prop)
    (selected : Node → Bool) : Prop :=
  ∀ node, children node (owner node) → selected node = false

/-- The SCC-local production rows, written in the exact algebraic orientation
used by Rust: parent - child - m * selected >= 1 - m. Only fibers with m > 1
have ranks or rows, and every row has both endpoints in that same fiber. -/
def SCCConstraints (owner : Node → Class) (children : Node → Class → Prop)
    (selected : Node → Bool) (component : Class → Label) (rank : SCCRanks component) : Prop :=
  ∀ label hlarge, BoundedRank (rank label hlarge) ∧
    ∀ node (parent child : Component component label),
      owner node = parent.val → children node child.val →
      1 - (Fintype.card (Component component label) : ℝ) ≤
        rank label hlarge parent - rank label hlarge child -
          (Fintype.card (Component component label) : ℝ) * bit (selected node)

/-- Under local bounds, the production row is exactly an implication guarded
by the Boolean selection. This is the global M = n theorem on a fiber. -/
theorem component_row_iff (component : Class → Label) (label : Label)
    (rank : Component component label → ℝ) (hbound : BoundedRank rank)
    (parent child : Component component label) (selected : Bool) :
    1 - (Fintype.card (Component component label) : ℝ) ≤
        rank parent - rank child - (Fintype.card (Component component label) : ℝ) * bit selected ↔
      (selected = true → rank child + 1 ≤ rank parent) := by
  rw [← conditional_iff rank hbound parent child selected]
  constructor <;> intro h <;> nlinarith

/-- A component of size at most one has no selected internal edge once direct
self-loop e-nodes have been disabled. -/
theorem singleton_component_has_no_edges (owner : Node → Class)
    (children : Node → Class → Prop) (selected : Node → Bool)
    (component : Class → Label) (label : Label)
    (hsmall : Fintype.card (Component component label) ≤ 1)
    (hself : SelfLoopsDisabled owner children selected)
    (parent child : Component component label) :
    ¬ ComponentEdge (SelectedEdge owner children selected) component label parent child := by
  haveI : Subsingleton (Component component label) :=
    Fintype.card_le_one_iff_subsingleton.mp hsmall
  have heq : parent.val = child.val := congrArg Subtype.val (Subsingleton.elim parent child)
  rintro ⟨node, hselected, howner, hchild⟩
  have hloop : children node (owner node) := by simpa only [howner, heq] using hchild
  have := hself node hloop
  simp [hselected] at this

/-- Main production-encoding theorem. For any cycle-preserving partition of
the full possible-edge graph, SCC-local rank rows plus direct self-loop
exclusion admit exactly the acyclic Boolean selections. The rank witness has
no entries for singleton components. No Rust or numerical solver is modeled. -/
theorem scc_encoding_sound_and_complete (owner : Node → Class)
    (children : Node → Class → Prop) (selected : Node → Bool)
    (component : Class → Label)
    (hpart : CyclePartition (PossibleEdge owner children) component) :
    Acyclic (SelectedEdge owner children selected) ↔
      SelfLoopsDisabled owner children selected ∧
        ∃ rank : SCCRanks component, SCCConstraints owner children selected component rank := by
  let edge := SelectedEdge owner children selected
  have hcomponent := acyclic_iff_components (PossibleEdge owner children) edge component
    (selected_subrelation_possible owner children selected) hpart
  constructor
  · intro hacyc
    have hlocal := hcomponent.mp hacyc
    have hwitness := fun label =>
      bounded_rank_exists (ComponentEdge edge component label) (hlocal label)
    let rank : SCCRanks component := fun label _ => Classical.choose (hwitness label)
    refine ⟨?_, rank, ?_⟩
    · intro node hself
      cases hselected : selected node with
      | false => rfl
      | true =>
          exact False.elim
            (selected_self_loop_impossible owner children selected hacyc node hself hselected)
    · intro label hlarge
      have hbound := (Classical.choose_spec (hwitness label)).1
      have hedges := (Classical.choose_spec (hwitness label)).2
      refine ⟨hbound, ?_⟩
      intro node parent child howner hchild
      apply (component_row_iff component label (rank label hlarge) hbound parent child
        (selected node)).mpr
      intro hselected
      exact hedges parent child ⟨node, hselected, howner, hchild⟩
  · rintro ⟨hself, rank, hconstraints⟩
    apply hcomponent.mpr
    intro label
    by_cases hlarge : 1 < Fintype.card (Component component label)
    · apply rank_sound (ComponentEdge edge component label) (rank label hlarge)
      rintro parent child ⟨node, hselected, howner, hchild⟩
      exact (component_row_iff component label (rank label hlarge)
        (hconstraints label hlarge).1 parent child (selected node)).mp
          ((hconstraints label hlarge).2 node parent child howner hchild) hselected
    · apply rank_sound (ComponentEdge edge component label) (fun _ => 0)
      intro parent child hedge
      exact False.elim (singleton_component_has_no_edges owner children selected component label
        (by omega) hself parent child hedge)

/-- Exact SCCs satisfy the sufficient partition assumption used above. -/
theorem exact_scc_encoding_sound_and_complete (owner : Node → Class)
    (children : Node → Class → Prop) (selected : Node → Bool)
    (component : Class → Label)
    (hpart : ExactSCCPartition (PossibleEdge owner children) component) :
    Acyclic (SelectedEdge owner children selected) ↔
      SelfLoopsDisabled owner children selected ∧
        ∃ rank : SCCRanks component, SCCConstraints owner children selected component rank := by
  exact scc_encoding_sound_and_complete owner children selected component
    (exact_scc_partition_is_cycle_partition _ _ hpart)

end Components

section Objective

variable [Fintype Node]

/-- The model's additive objective, counting each selected e-node once. -/
def objective (cost : Node → ℝ) (selected : Node → Bool) : ℝ :=
  ∑ node, cost node * bit (selected node)

omit [Fintype Class] in
/-- Pruning any subset of selected e-nodes cannot increase nonnegative additive cost.

The caller must separately establish that its pruning operation preserves roots,
closure under selected children, and one selected e-node per active class.
-/
theorem objective_subset_le (cost : Node → ℝ) (selected kept : Node → Bool)
    (hnonneg : ∀ node, 0 ≤ cost node)
    (hsubset : ∀ node, kept node = true → selected node = true) :
    objective cost kept ≤ objective cost selected := by
  apply Finset.sum_le_sum
  intro node _
  cases hk : kept node <;> cases hs : selected node
  · simp [bit]
  · simpa [bit, hk, hs] using hnonneg node
  · have := hsubset node hk
    simp [hs] at this
  · simp [bit]

end Objective

-- Kernel axiom reports are part of the build evidence. They must contain no sorryAx.
#print axioms acyclic_iff_internal
#print axioms acyclic_iff_components
#print axioms component_row_iff
#print axioms singleton_component_has_no_edges
#print axioms scc_encoding_sound_and_complete
#print axioms exact_scc_encoding_sound_and_complete
#print axioms encoding_sound_and_complete
#print axioms selected_self_loop_impossible
#print axioms objective_subset_le

end EggLpRank
