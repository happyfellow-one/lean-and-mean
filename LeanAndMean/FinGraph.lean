import Mathlib

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

theorem dfs_sound
    (nodes : V → Finset V)
    (visited : Finset V)
    (v w : V)
    (h : w ∈ dfs v nodes visited) :
    w ∈ visited ∪ {v} ∨ Reachable nodes v w := by
  fun_induction dfs v nodes visited
  · grind
  · expose_names
    by_cases w ∈ visited
    case pos => grind
    case neg hwin =>
      rw [Finset.mem_union] at h
      cases h with
      | inl h => left; assumption
      | inr h =>
        rw [Finset.mem_biUnion] at h
        rcases h with ⟨a, hanode, hwin'⟩
        have ih : w ∈ visited' ∪ {a} ∨ Reachable nodes a w := by apply ih1; grind
        cases ih with
        | inl ih =>
          rw [Finset.mem_union] at ih
          cases ih with
          | inl ih => left; trivial
          | inr ih =>
            rw [Finset.mem_singleton] at ih
            rw [ih] at *
            right
            apply Relation.ReflTransGen.single
            trivial
        | inr ih =>
          right
          have : Reachable nodes v a := by apply Relation.ReflTransGen.single; trivial
          apply Relation.ReflTransGen.trans (b := a) <;> trivial

@[simp]
def Walk (nodes : V → Finset V) (w : List V) := w.IsChain (fun x y => y ∈ nodes x)

@[simp]
def SimpleWalk (nodes : V → Finset V) (w : List V) := Walk nodes w ∧ w.Nodup

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

theorem List.getLast_split
    {α : Type}
    [DecidableEq α]
    (l : List α)
    (hnonempty : l ≠ [])
    (x : α)
    (h : l.getLast hnonempty = x) :
    ∃ l1, l = l1 ++ [x] := by
  use l.take (l.length -1)
  apply List.ext_getElem
  · grind
  · intro i h₁ h₂
    by_cases i < l.length - 1 <;> grind

theorem List.mem_split_last
    {α : Type}
    [DecidableEq α]
    (l : List α)
    (x : α)
    (h : x ∈ l) :
    ∃ l1 l2, l = l1 ++ [x] ++ l2 ∧ x ∉ l2 := by
  induction l with
  | nil => simp at h
  | cons head tail ih =>
    by_cases x = head
    case pos heq =>
      by_cases x ∈ tail
      case neg h => use [], tail; grind
      case pos h =>
        rcases ih h with ⟨ l1, l2, heq, hnotin ⟩
        use (x :: l1), l2; grind
    case neg heq =>
      rcases ih (by grind) with ⟨ l1, l2, heq, hnotin ⟩
      use (head :: l1), l2; grind

omit [Fintype V] in
theorem simple_walk_of_reachable
    (nodes : V → Finset V)
    (v w : V)
    (reachable : Reachable nodes v w) :
    ∃ vs, SimpleWalk nodes (v :: vs) /\ (v :: vs).getLast (by grind) = w := by
  induction reachable with
  | refl =>
    use []
    repeat constructor <;> simp
  | tail hrel hnode a_ih =>
    expose_names
    rcases a_ih with ⟨vs, walk, hlast⟩
    by_cases c ∈ (v :: vs)
    case neg h =>
      use (vs ++ [c])
      constructor
      · have : ∃ vs₁, v :: vs = vs₁ ++ [b] := by
          apply List.getLast_split; trivial
        rcases this with ⟨vs₁, heq⟩
        rw [←List.cons_append, heq]
        simp only [SimpleWalk, Walk]
        constructor
        · simp; constructor
          · rw [←heq]; exact walk.1
          · trivial
        · rw [←heq]
          have : (v :: vs).Nodup := walk.2
          grind
      · simp
    case pos h =>
      have hpart : ∃ vs₁ vs₂, v :: vs = vs₁ ++ [c] ++ vs₂ ∧ c ∉ vs₂ := by
        apply List.mem_split_last
        trivial
      rcases hpart with ⟨vs₁, vs₂, hpart, hpartnot⟩
      rw [hpart] at walk
      rcases SimpleWalk.partition walk with ⟨h1, _⟩
      have hhead : ∃ vs', vs₁ ++ [c] = v :: vs' := by
        cases vs₁ with
        | nil => use []; simp at hpart; grind
        | cons head tail => use (tail ++ [c]); grind
      rcases hhead with ⟨vs', hhead⟩
      use vs'
      constructor
      · rw [←hhead]; trivial
      · apply List.getLast_of_getLast?_eq_some
        rw [←hhead]; simp

theorem dfs_complete_walk
    (v : V)
    (vs : List V)
    (nodes : V → Finset V)
    (visited : Finset V)
    (walk : SimpleWalk nodes (v :: vs))
    (h : ∀ x ∈ visited, x ∉ v :: vs) :
    (v :: vs).getLast (by grind) ∈ dfs v nodes visited := by
  cases vs with
  | nil => unfold dfs; grind
  | cons v₂ vs =>
    expose_names
    unfold dfs
    by_cases v ∈ visited
    case pos h' => grind
    case neg h' =>
      simp [h']
      right
      by_cases (v₂ :: vs).getLast (by grind) ∈ visited
      case pos h'' => left; grind
      case neg h'' =>
        rcases walk with ⟨walk, hnodup⟩
        unfold Walk at walk
        right
        use v₂
        constructor
        · grind
        · apply dfs_complete_walk
          · unfold SimpleWalk; unfold Walk; grind
          · intro x hin hin'
            rw [Finset.mem_insert] at hin
            cases hin with
            | inl hin => rw [←hin] at hnodup; grind
            | inr hin =>
              have : x ∉ v :: v₂ :: vs := by apply h; trivial
              grind

def dfs_complete
    (v w : V)
    (nodes : V → Finset V)
    (reachable : Reachable nodes v w) :
    w ∈ dfs v nodes ∅ := by
  have walk : ∃ vs, SimpleWalk nodes (v :: vs) ∧ (v :: vs).getLast (by grind) = w := by
    apply simple_walk_of_reachable
    trivial
  rcases walk with ⟨vs, walk, hlast⟩
  have : (v :: vs).getLast (by grind) ∈ dfs v nodes ∅ := by
    apply dfs_complete_walk v vs
    · trivial
    · grind
  rw [hlast] at this
  apply this
