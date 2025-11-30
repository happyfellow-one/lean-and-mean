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
    w ∈ visited ∪ {v} ∨ Reachable (nodes := nodes) v w := by
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

lemma dfs_expansive
    (v : V)
    (nodes : V → Finset V)
    (visited : Finset V) :
    visited ∪ {v} ⊆ dfs v nodes visited := by
  fun_induction dfs v nodes visited <;> grind

inductive SimpleWalk (nodes : V → Finset V) : List V → Prop where
| empty : (v : V) → SimpleWalk nodes [v]
| step :
  {v₁ v₂ : V} →
  {vs : List V} →
  v₂ ∈ nodes v₁ →
  SimpleWalk nodes (v₂ :: vs) →
  v₁ ∉ (v₂ :: vs) →
  SimpleWalk nodes (v₁ :: v₂ :: vs)

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

theorem SimpleWalk.subwalk
    {nodes : V → Finset V}
    {vs vs₁ vs₂ vs₃}
    (walk : SimpleWalk nodes vs)
    (hpart : vs = vs₁ ++ vs₂ ++ vs₃)
    (hnonempty : vs₂ ≠ []) :
    SimpleWalk nodes vs₂ := by
  rcases walk.partition hpart with ⟨h1, h2⟩
  have : vs₁ ++ vs₂ ≠ [] := by
    apply List.append_ne_nil_of_right_ne_nil
    trivial
  have h1 : SimpleWalk nodes (vs₁ ++ vs₂) := by apply h1; trivial
  rcases h1.partition (vs := vs₁ ++ vs₂) (vs₁ := vs₁) (vs₂ := vs₂) (hpart := by grind) with ⟨h1, h2⟩
  apply h2
  trivial

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
      sorry


/-
To prove completeness:
 - Show that Reachable implies simple walk.
 - IH: if Reachable v w then
-/

theorem dfs_complete
    (start v w : V)
    (nodes : V → Finset V)
    (visited : Finset V)
    (h : Reachable nodes start w) :
    w ∈ dfs v nodes visited := by
  induction h generalizing visited with
  | refl v =>
    have hexp : visited ∪ {v} ⊆ dfs v nodes visited := by apply dfs_expansive
    grind
  | step =>
    expose_names
    unfold dfs

    sorry
