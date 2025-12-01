import Mathlib

/-!
# DFS works!

Below you'll find an implementation of a DFS-like graph traversal, together with:

- soundness proof: all nodes returned by dfs are reachable from the starting point,
- completeness proof: all reachable nodes are returned by the dfs.

One-step adjacency is represented by nodes function.

As far as I can tell, it's Lean tradition to start with a random looking List lemma:
-/

lemma List.getLast_split
    {α : Type}
    [DecidableEq α]
    (l : List α)
    (hnonempty : l ≠ []) :
    ∃ l1, l = l1 ++ [l.getLast hnonempty] := by
  use l.take (l.length -1)
  apply List.ext_getElem
  · grind
  · intro i h₁ h₂; by_cases i < l.length - 1 <;> grind

variable {V : Type} [Fintype V] [DecidableEq V]

def dfs [Fintype V] (v : V) (nodes : V → Finset V) (visited : Finset V) : Finset V :=
  if _hin : v ∈ visited
  then visited
  else
    let visited' := visited ∪ {v}
    visited' ∪ Finset.biUnion (nodes v) (fun w => dfs w nodes visited')
termination_by (Fintype.card V - visited.card)
decreasing_by
  have hlt : visited.card < (visited ∪ {v}).card := by grind
  apply Nat.sub_lt_sub_left
  · apply Finset.card_lt_univ_of_notMem _hin
  · assumption

def Reachable (nodes : V → Finset V) := Relation.ReflTransGen (fun x y => y ∈ nodes x)

-- Each node returned by dfs is reachable from v:
theorem dfs_sound
    (nodes : V → Finset V)
    (visited : Finset V)
    (v w : V)
    (h : w ∈ dfs v nodes visited) :
    w ∈ visited ∪ {v} ∨ Reachable nodes v w := by
  fun_induction dfs v nodes visited with
  | case1 => grind
  | case2 v _ _ _ ih =>
    cases cast (Iff.eq Finset.mem_union) h with
    | inl => grind
    | inr h =>
      rcases cast (Iff.eq Finset.mem_biUnion) h with ⟨a, hanode, hwin'⟩
      have _ : Reachable nodes v a := by apply Relation.ReflTransGen.single; trivial
      cases ih a hwin' with
      | inl => grind
      | inr ih => right; apply Relation.ReflTransGen.trans (b := a) <;> trivial

/-!
To prove completeness, we need to show that if w if reachable from v, then there
exists a simple walk: a path starting at v, ending at w which doesn't repeat any
nodes.
-/

@[simp]
def Walk (nodes : V → Finset V) (w : List V) := w.IsChain (fun x y => y ∈ nodes x)

@[simp]
def SimpleWalk (nodes : V → Finset V) (w : List V) := Walk nodes w ∧ w.Nodup

-- You can split walks in parts:
omit [Fintype V] [DecidableEq V] in
theorem SimpleWalk.partition
    {nodes : V → Finset V}
    {vs₁ vs₂}
    (walk : SimpleWalk nodes (vs₁ ++ vs₂)) :
    SimpleWalk nodes vs₁ ∧ SimpleWalk nodes vs₂ := by
  rcases walk with ⟨walk, hnodup⟩
  simp at walk
  constructor
  <;> constructor
  <;> first
    | simpa [Walk] using List.IsChain.left_of_append walk
    | simpa [Walk] using List.IsChain.right_of_append walk
    | grind

-- You can truncate a walk at any intermediate point:
omit [Fintype V] [DecidableEq V] in
theorem SimpleWalk.truncate
    (nodes : V → Finset V)
    (v w : V)
    (vs : List V)
    (walk : SimpleWalk nodes (v :: vs))
    (h : w ∈ (v :: vs)) :
    ∃ vs', SimpleWalk nodes (v :: vs') ∧ (v :: vs').getLast (by grind) = w := by
  have : ∃ vs₁ vs₂, v :: vs = vs₁ ++ [w] ++ vs₂ := by
    simp; rw [←List.mem_iff_append]; trivial
  rcases this with ⟨vs₁, vs₂, heq⟩
  rw [heq] at walk
  rcases SimpleWalk.partition walk with ⟨h, _⟩
  have : ∃ vs', vs₁ ++ [w] = v :: vs' := by cases h : vs₁ ++ [w] <;> grind
  rcases this with ⟨vs', heq⟩
  grind

-- You can extend a walk by an extra edge:
omit [Fintype V] in
theorem SimpleWalk.append
    (nodes : V → Finset V)
    (v w : V)
    (vs : List V)
    (walk : SimpleWalk nodes (v :: vs))
    (h₁ : w ∉ v :: vs)
    (h₂ : w ∈ nodes ((v :: vs).getLast (by grind))) :
    SimpleWalk nodes (v :: vs ++ [w]) := by
  rcases List.getLast_split (v :: vs) (by grind) with ⟨vs', h⟩
  rcases walk with ⟨walk, hnodup⟩
  constructor
  · unfold Walk
    apply List.IsChain.append <;> first | exact walk | grind
  · grind -- nodup

omit [Fintype V] in
theorem SimpleWalk.of_reachable
    (nodes : V → Finset V)
    (v w : V)
    (reachable : Reachable nodes v w) :
    ∃ vs, SimpleWalk nodes (v :: vs) /\ (v :: vs).getLast (by grind) = w := by
  induction reachable with
  | refl => use []; repeat constructor <;> simp
  | @tail b c hrel hnode a_ih =>
    rcases a_ih with ⟨vs, walk, hlast⟩
    by_cases c ∈ (v :: vs)
    case pos h =>
      -- If c is in the walk, we're done: we just truncate it to c
      apply SimpleWalk.truncate <;> assumption
    case neg h =>
     -- Otherwise, we know that extending the walk with c won't repeat any nodes:
      use (vs ++ [c])
      constructor
      · rw [←List.cons_append]; apply SimpleWalk.append <;> grind
      · simp

theorem dfs_complete_walk
    (v : V)
    (vs : List V)
    (nodes : V → Finset V)
    (visited : Finset V)
    (walk : SimpleWalk nodes (v :: vs))
    (h : ∀ x ∈ visited, x ∉ v :: vs) :
    (v :: vs).getLast (by grind) ∈ dfs v nodes visited := by
  fun_induction dfs v nodes visited generalizing vs
  case case1 => grind
  case case2 _ v visited hnotin visited' ih =>
    let last := (v :: vs).getLast (by grind)
    by_cases last ∈ visited'
    case pos => grind
    case neg hnotinlast =>
      apply Finset.mem_union_right
      rw [Finset.mem_biUnion]
      cases vs with
      | nil => grind -- walk ends here
      | cons head tail =>
        use head
        have _ : head ∈ nodes v := by simp at walk; grind
        have _ : SimpleWalk nodes (head :: tail) := by simp at walk; simp; grind
        have _ : ∀ x ∈ visited', x ∉ head :: tail := by unfold visited'; simp at walk; grind
        constructor <;> grind

def dfs_complete
    (v w : V)
    (nodes : V → Finset V)
    (reachable : Reachable nodes v w) :
    w ∈ dfs v nodes ∅ := by
  have walk : ∃ vs, SimpleWalk nodes (v :: vs) ∧ (v :: vs).getLast (by grind) = w := by
    apply SimpleWalk.of_reachable
    trivial
  rcases walk with ⟨vs, walk, hlast⟩
  have : (v :: vs).getLast (by grind) ∈ dfs v nodes ∅ := by
    apply dfs_complete_walk v vs <;> grind
  rw [hlast] at this
  apply this
