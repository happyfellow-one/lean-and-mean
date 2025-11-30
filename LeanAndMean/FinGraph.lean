import Mathlib

variable {V : Type} [Fintype V] [DecidableEq V]

def dfs [Fintype V] (v : V) (nodes : V → Finset V) (visited : Finset V) : Finset V :=
  if hin : v ∈ visited
  then visited
  else
    let visited' := visited ∪ {v}
    visited' ∪ Finset.biUnion (nodes v) (fun w => dfs w nodes visited')
termination_by (Fintype.card V - visited.card)
decreasing_by
  have hlt : visited.card < (visited ∪ {v}).card := by grind
  apply Nat.sub_lt_sub_left
  · apply Finset.card_lt_univ_of_notMem hin
  · assumption

inductive Reachable (nodes : V → Finset V) : V → V → Prop where
| refl : (v : V) → Reachable nodes v v
| step : {v₁ v₂ v₃ : V} → v₂ ∈ nodes v₁ → Reachable nodes v₂ v₃ → Reachable nodes v₁ v₃

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
            apply Reachable.step (v₁ := v) (v₂ := a) (v₃ := a)
            · trivial
            · constructor
        | inr ih =>
          right
          apply Reachable.step (v₁ := v) (v₂ := a) (v₃ := w)
          · trivial
          · trivial

inductive SimpleWalk (nodes : V → Finset V) : List V → Prop where
| empty : (v : V) → SimpleWalk nodes [v]
| step :
  {v₁ v₂ : V} →
  {vs : List V} →
  v₂ ∈ nodes v₁ →
  SimpleWalk nodes (v₂ :: vs) →
  v₁ ∉ (v₂ :: vs) →
  SimpleWalk nodes (v₁ :: v₂ :: vs)

theorem SimpleWalk.middle_edge
    {nodes : V → Finset V}
    {vs₁ vs₂}
    {v₁ v₂}
    (walk : SimpleWalk nodes (vs₁ ++ [v₁, v₂] ++ vs₂)) :
    v₂ ∈ nodes v₁ := by
  induction vs₁ generalizing vs₂ with
  | nil =>
    cases walk; trivial
  | cons head tail ih =>
    simp at walk
    cases tail with
    | nil =>
      simp at walk
      cases walk
      apply ih
      assumption
    | cons head1 tail =>
      cases walk
      apply ih
      · simp; assumption

theorem SimpleWalk.partition
    {nodes : V → Finset V}
    {vs vs₁ vs₂}
    (walk : SimpleWalk nodes vs)
    (hpart : vs = vs₁ ++ vs₂) :
    (vs₁ ≠ [] → SimpleWalk nodes vs₁)
    ∧ (vs₂ ≠ [] → SimpleWalk nodes vs₂) := by
  induction walk generalizing vs₁ vs₂
  case empty v =>
    have : vs₁ = [v] ∨ vs₂ = [v] := by
      cases vs₁ <;> cases vs₂ <;> simp at hpart <;> grind
    constructor <;> intros <;> cases this <;> simp_all <;> constructor
  case step =>
    expose_names
    cases vs₁ with
    | nil =>
      constructor <;> intros <;> try contradiction
      simp at hpart
      rw [←hpart]
      constructor <;> assumption
    | cons head tail =>
      have hhead : head = v₁ := by grind
      have hpart' : v₂ :: vs_1 = tail ++ vs₂ := by grind
      have : (tail ≠ [] → SimpleWalk nodes tail) ∧ (vs₂ ≠ [] → SimpleWalk nodes vs₂) := by
        apply a_ih; trivial
      rcases this with ⟨ih1, ih2⟩
      constructor
      · intro _
        rw [hhead]
        cases tail with
        | nil => constructor
        | cons head' tail =>
          have hhead' : head' = v₂ := by grind
          constructor
          · rw [hhead']; trivial
          · apply ih1; grind
          · grind
      · intro hne
        apply ih2
        trivial

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

theorem simple_walk_of_reachable
    (nodes : V → Finset V)
    (v w : V)
    (reachable : Reachable nodes v w) :
    ∃ vs, SimpleWalk nodes (v :: vs) /\ (v :: vs).getLast (by grind) = w := by
  induction reachable with
  | refl a =>
    use []
    constructor
    · constructor
    · simp
  | step =>
    expose_names
    rcases a_ih with ⟨vs, walk, hlast⟩
    by_cases v₁ ∈ (v₂ :: vs)
    case neg hv =>
      use (v₂ :: vs)
      constructor
      · constructor <;> grind
      · grind
    case pos hv =>
      have hpart : ∃ vs₁ vs₂, v₂ :: vs = vs₁ ++ [v₁] ++ vs₂ ∧ v₁ ∉ vs₂ := by
        apply List.mem_split_last
        trivial
      rcases hpart with ⟨vs₁, vs₂, hpart, hpartnot⟩
      rcases walk.partition hpart with ⟨h1, h2⟩
      cases vs₂ with
      | nil =>
        use []
        constructor
        · constructor
        · grind
      | cons v₂_head v₂_tail =>
        use (v₂_head :: v₂_tail)
        constructor
        · constructor
          · rw [hpart] at walk
            rw [List.append_cons] at walk
            conv at walk =>
              arg 2
              arg 1
              rw [List.append_assoc]
              arg 2
              simp
            apply SimpleWalk.middle_edge
            trivial
          · apply h2; grind
          · grind
        · grind

theorem dfs_complete_walk
    (v : V)
    (vs : List V)
    (nodes : V → Finset V)
    (visited : Finset V)
    (walk : SimpleWalk nodes (v :: vs))
    (h : ∀ x ∈ visited, x ∉ v :: vs) :
    (v :: vs).getLast (by grind) ∈ dfs v nodes visited := by
  cases walk with
  | empty v => unfold dfs; grind
  | step =>
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
        right
        use v₂
        constructor
        · trivial
        · apply dfs_complete_walk
          · trivial
          · intro x hin hin'
            rw [Finset.mem_insert] at hin
            cases hin with
            | inl hin => rw [←hin] at h_3; contradiction
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
