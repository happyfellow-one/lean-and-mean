import Mathlib

/-!
# Konig's Lemma

Every finitely-branching infinite tree has an infinite path. Sounds easy, let's
try a lean formalisation.
-/

inductive IsDescendant {V : Type} (children : V → List V) : V → V → Prop where
| direct : (v : V) → IsDescendant children v v
| step :
  (v v' v'' : V) →
  v' ∈ children v →
  IsDescendant children v' v'' →
  IsDescendant children v v''

/-- Infinite rooted tree with finite branching. -/
structure RootedLocallyFiniteTree where
  V : Type
  root : V
  children : V → List V
  infiniteDescendants :  { v | IsDescendant children root v }.Infinite

@[grind, simp]
def RootedLocallyFiniteTree.IsDescendant'
    (tree : RootedLocallyFiniteTree)
    (v w : tree.V) : Prop :=
  IsDescendant tree.children v w

@[grind, simp]
def RootedLocallyFiniteTree.descendants
    (tree : RootedLocallyFiniteTree)
    (start : tree.V) :
    Set tree.V :=
  { v | tree.IsDescendant' start v }

@[grind =]
theorem RootedLocallyFiniteTree.descendants_decomposition
    (tree : RootedLocallyFiniteTree)
    (v : tree.V) :
    tree.descendants v = {v} ∪
    ⋃ (v' ∈ {x | x ∈ tree.children v}), tree.descendants v' := by
  apply Set.ext
  intro x
  constructor
  · intro hx
    cases hx
    · grind
    · expose_names
      have : x ∈ tree.descendants v' := by grind
      apply Set.mem_union_right
      rw [Set.mem_iUnion]
      use v'
      simp
      grind
  · intro h
    cases h with
    | inl h =>
      cases h
      simp
      constructor
    | inr h =>
      have : ∃ (v' : { w // w ∈ tree.children v }), x ∈ tree.descendants v' := by
        rw [Set.mem_iUnion] at h
        simp at h
        obtain ⟨ v', hv', h ⟩ := h
        use ⟨v', hv'⟩
        grind
      obtain ⟨ v', h' ⟩ := this
      apply IsDescendant.step (v' := v'.1)
      · exact v'.2
      · grind

def finite_children_descendants
    (tree : RootedLocallyFiniteTree)
    (v : tree.V)
    (h : ∀ w ∈ tree.children v, (tree.descendants w).Finite) :
    (tree.descendants v).Finite := by
  rw [tree.descendants_decomposition]
  rw [Set.finite_union]
  constructor
  · apply Set.finite_singleton
  · have : {x | x ∈ tree.children v}.Finite := by simp
    have : Finite {x | x ∈ tree.children v} := by
      simp_rw [Set.finite_coe_iff]
      trivial
    rw [Set.biUnion_eq_iUnion]
    apply Set.finite_iUnion
    grind

lemma infinite_descendants_step
    (tree : RootedLocallyFiniteTree)
    (v : tree.V)
    (hv : (tree.descendants v).Infinite) :
    ∃ w, w ∈ tree.children v ∧ (tree.descendants w).Infinite := by
  by_contra h
  push_neg at h
  suffices : (tree.descendants v).Finite
  · exact (hv this)
  apply finite_children_descendants
  simpa [Set.not_infinite] using h

structure InfiniteWalk (tree : RootedLocallyFiniteTree) where
  node : ℕ → tree.V
  properWalk : ∀ i, node (i + 1) ∈ tree.children (node i)

noncomputable
def konig_node
    (tree : RootedLocallyFiniteTree)
    (n : ℕ) : Σ' v, (tree.descendants v).Infinite :=
  match n with
  | .zero => ⟨tree.root, tree.infiniteDescendants⟩
  | .succ n =>
    let ⟨prev, hprev⟩ : Σ' prev, (tree.descendants prev).Infinite := konig_node tree n
    have inf : ∃ w ∈ tree.children prev, (tree.descendants w).Infinite :=
      infinite_descendants_step tree prev hprev
    ⟨ Classical.choose inf
    , by apply (Classical.choose_spec (h := inf)).2 ⟩

theorem konigLemma'
    (tree : RootedLocallyFiniteTree) :
    Nonempty (InfiniteWalk tree) := by
  classical
  let node (n : ℕ) : tree.V := (konig_node tree n).1
  have properWalk (i : ℕ) : node (i + 1) ∈ tree.children (node i) := by
    suffices : node (i+1) ∈ tree.children (node i) ∧ (tree.descendants (node (i+1))).Infinite
    · exact this.1
    simp [node, konig_node]
    apply Classical.choose_spec
      (p := (fun x => x ∈ tree.children (node i) ∧ (tree.descendants x).Infinite))
  constructor
  exact { node := node, properWalk := properWalk }
