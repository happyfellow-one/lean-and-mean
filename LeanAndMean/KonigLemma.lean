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
  infiniteDescendants : Infinite { v // IsDescendant children root v }

def RootedLocallyFiniteTree.descendants
    (tree : RootedLocallyFiniteTree)
    (start : tree.V) :
    Type :=
  { v // IsDescendant tree.children start v }

lemma infinite_descendants_step
    (tree : RootedLocallyFiniteTree) :
    ∃ v, v ∈ tree.children tree.root
         ∧ Infinite (tree.descendants v) := by
  apply Classical.by_contradiction
  intros h
  rw [<-Classical.not_forall_not, Classical.not_not] at h
  have hfin : ∀ x ∈ tree.children tree.root, Finite (tree.descendants x) :=
    sorry
  suffices : Finite (tree.descendants tree.root)
  · have : ¬Infinite (tree.descendants tree.root) := by
      apply Finite.not_infinite this
    exact (this tree.infiniteDescendants)
  have hfintype : ∀ x ∈ tree.children tree.root, Fintype (tree.descendants x) := by
    intro x hxmem
    have : Finite (tree.descendants x) := hfin x hxmem
    apply Fintype.ofFinite
  let totalSize : ℕ :=
    (tree.children tree.root).attach.map (fun (⟨x, xmem⟩ : { x // x ∈ tree.children tree.root })=>
      let _ : Fintype _ := (hfintype x xmem)
      Fintype.card (tree.descendants x)
    )
    |> List.sum
  -- I need to check whether the root is contained in descendants or not, to know whether
  -- I should add one for the root or not. Then I know the cardinality, so I can choose
  -- proper Fin n.
  sorry

structure InfiniteWalk (tree : RootedLocallyFiniteTree) where
  node : ℕ → tree.V
  properWalk : ∀ i, node (i + 1) ∈ tree.children (node i)

def konigLemma'
    (tree : RootedLocallyFiniteTree)
    [Infinite tree.V] :
    InfiniteWalk tree := by
  sorry
