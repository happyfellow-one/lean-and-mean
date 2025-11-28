import Mathlib

-- We're using native decide just for the examples
set_option linter.style.nativeDecide false

inductive Operation | add | sub | mul | div
  deriving DecidableEq

def Operation.parse (input : String) : Option Operation :=
  match input with
  | "+" => .some .add | "-" => .some .sub
  | "*" => .some .mul | "/" => .some .div
  | _ => .none

def Operation.eval (operation : Operation) : ℕ → ℕ → ℕ :=
  match operation with
  | .add => Nat.add
  | .sub => Nat.sub
  | .mul => Nat.mul
  | .div => Nat.div

inductive Token where
| const : ℕ → Token
| op : Operation → Token
  deriving DecidableEq

def Token.parse (input : String) : Option Token :=
  match Operation.parse input with
  | .some operation => Option.some (Token.op operation)
  | .none => input.toNat?.map (fun x => Token.const x)

abbrev Program := List Token

def parse (input : String) : Option (List Token) :=
  (input.splitToList (·.isWhitespace)).map Token.parse
  |> sequence

example : parse "10 20 +" = .some [.const 10, .const 20, .op .add] := by
  native_decide

example : parse "+ -10" = .none := by native_decide

def eval_rpn (program : Program) (stack : List ℕ) : Option (List ℕ) :=
  match program with
  | [] => .some stack
  | (.const n) :: program => eval_rpn program (n :: stack)
  | (.op operation) :: program =>
    match stack with
    | a :: b :: stack => eval_rpn program (operation.eval b a :: stack)
    | _ => .none

example : eval_rpn [.const 10, .const 10, .op .mul] [] = .some [100] := by
  native_decide


inductive Term where
| const : ℕ → Term
| op : Operation → Term → Term → Term
  deriving DecidableEq

def Term.eval (t : Term) : ℕ :=
  match t with
  | .const n => n
  | .op operation t1 t2 => operation.eval t1.eval t2.eval

example : (Term.op .add (.const 10) (.const 20)).eval = 30 := by native_decide

def Term.rpn (t : Term) : Program :=
  match t with
  | .const n => [.const n]
  | .op operation t1 t2 => t1.rpn ++ t2.rpn ++ [.op operation]

example : (Term.op .add (.const 10) (.const 20)).rpn = [.const 10, .const 20, .op .add] := by
  native_decide

lemma rpn_append
    (p1 p2 : Program)
    (s : List ℕ) :
    eval_rpn (p1 ++ p2) s = Option.bind (eval_rpn p1 s) (eval_rpn p2) := by
  induction p1 generalizing s
  case nil => simp [eval_rpn]
  case cons head tail ih =>
    cases head
    case const => simp [eval_rpn, ih]
    case op operation =>
      simp [eval_rpn, ih]
      cases s
      case' cons _ s => cases s
      case' cons.cons _ s => cases s
      all_goals simp

theorem rpnTranslationWorks
    (t : Term)
    (s : List ℕ) :
    eval_rpn t.rpn s = .some (t.eval :: s) := by
  induction t generalizing s
  case const n =>
    simp [eval_rpn, Term.rpn, Term.eval]
  case op operation t1 t2 ih1 ih2 =>
    simp [Term.rpn, rpn_append, ih1, ih2, eval_rpn, Term.eval]


-- Let's try the other way around!

def rpn_to_terms (program : Program) (s : List Term) : Option (List Term) :=
  match program with
  | []  => .some s
  | .const n :: program => rpn_to_terms program (.const n :: s)
  | .op operation :: program =>
    match s with
    | t1 :: t2 :: s => rpn_to_terms program (.op operation t2 t1 :: s)
    | _ => .none

example : rpn_to_terms [.const 10, .const 20, .op .sub] []
        = .some [.op .sub (.const 10) (.const 20)] := by
  native_decide

lemma rpn_to_terms_append (p1 p2 : Program) (s : List Term) :
    rpn_to_terms (p1 ++ p2) s = Option.bind (rpn_to_terms p1 s) (rpn_to_terms p2) := by
  induction p1 generalizing s
  case nil => simp [rpn_to_terms]
  case cons head tail ih =>
    cases head
    all_goals (simp [rpn_to_terms, ih])
    cases s
    case' op.cons _ s => cases s
    case' op.cons.cons _ s => cases s
    all_goals simp

theorem translationInv1
    (t : Term)
    (ts : List Term) :
    rpn_to_terms t.rpn ts = .some (t :: ts) := by
  induction t generalizing ts
  case const => simp [rpn_to_terms, Term.rpn]
  case op operation t1 t2 ih1 ih2 =>
    simp [Term.rpn, rpn_to_terms_append, ih1, ih2, rpn_to_terms]

-- eval is preserved:

theorem rpn_to_terms_eval
    (program : Program)
    (s : List Term) :
    eval_rpn program (s.map Term.eval)
    = (rpn_to_terms program s).map (fun x => x.map Term.eval) := by
  induction program generalizing s
  case nil => simp [eval_rpn, rpn_to_terms]
  case cons head tail ih =>
    cases head
    all_goals rw [<-List.singleton_append]
    all_goals simp [eval_rpn, rpn_to_terms]
    case const a =>
      conv => lhs; arg 2; change (List.map Term.eval (.const a :: s))
      rw [ih]
    case op operation =>
      cases s
      case' cons _ stail => cases stail
      all_goals simp
      case cons.cons head1 head2 tail =>
        conv => lhs; arg 2; change List.map Term.eval (.op operation head2 head1 :: tail)
        rw [ih]

/-
The next theorem is slightly tricky to prove: if we need to handle ill-formed RPN
programs such as "*" then we aren't certain that the result of rpn_to_terms partitions
into the result of translation and initial stack!

rpn_to_terms [.op .mul] [.const 10, .const 20] = [.op .mul (.const 10) (.const 20)]

We need to introduce a WellFormedProgram property, roughly meaning that executing that
RPN on an empty stack doesn't crash, which will allow us to prove the inverse theorem.
-/

-- StackSignature p c m == stack +c at the end, requires minimum m elements at start
-- to execute properly. If m is less than 0, it means it doesn't touch that many elements
-- at the bottom of the stack.
inductive StackSignature : Program → Int → Int → Prop where
| nil : StackSignature [] 0 0
| const {program : Program} {c m : ℤ} (n : ℕ) :
  StackSignature program c m →
  StackSignature (.const n :: program) (c+1) (m-1)
| op {program : Program} {c m : ℤ} (operation : Operation) :
  StackSignature program c m →
  StackSignature (.op operation :: program) (c-1) (max 2 (m+2))

def WellFormedProgram (p : Program) : Prop := ∃ c, ∃ m ≤ 0, StackSignature p c m

-- Sanity checking: evaluation should always work on well formed programs:

lemma wellFormedEval
    {c m : ℤ}
    (p : Program)
    (psd : StackSignature p c m) :
    ∀ (l : List ℕ) (_ : l.length ≥ m),
    ∃ s', eval_rpn p l = .some s' ∧ s'.length = l.length + c := by
  intro l hlen
  induction p generalizing l c m
  cases psd
  case nil.nil => exists l
  case cons head tail ih =>
    cases psd
    case const c m n psd =>
      have ⟨ s', a, b ⟩ : ∃ s', eval_rpn tail (n :: l) = .some s'
                                ∧ s'.length = (n :: l).length + c := by
        apply ih psd (n :: l); simp
        omega
      exists s'
      simp [eval_rpn]
      apply And.intro
      · assumption
      · simp at *; omega
    case op c m operation psd =>
      match l with
      | [] => simp at hlen
      | [_] => simp at hlen
      | h1 :: h2 :: l =>
        simp [eval_rpn]
        have ⟨s', a, b⟩ : ∃ s', eval_rpn tail (operation.eval h2 h1 :: l) = some s'
                                ∧ s'.length = l.length + 1 + c := by
          apply ih psd (operation.eval h2 h1 :: l)
          simp at hlen ⊢
          omega
        use s'

theorem translationInv2
    {c m : ℤ}
    (p : Program)
    (ss : StackSignature p c m)
    (ts : List Term)
    (htslen : ts.length ≥ m) :
    ∃ ts', rpn_to_terms p ts = .some ts'
           ∧ ts.reverse.flatMap (·.rpn) ++ p = ts'.reverse.flatMap (·.rpn) := by
  induction p generalizing ts c m
  case nil =>
    use ts
    simp [rpn_to_terms]
  case cons head tail ih =>
    cases head
    cases ss
    case const.const a c m ss =>
      have : ∃ ts', rpn_to_terms tail (.const a :: ts) = some ts'
             ∧ (.const a :: ts).reverse.flatMap (fun x => x.rpn) ++ tail
               = ts'.reverse.flatMap (fun x => x.rpn) := by
        apply (ih ss)
        simp
        omega
      obtain ⟨ts', heq1, heq2⟩ := this
      use ts'
      simp [rpn_to_terms]
      constructor
      · assumption
      · simp [Term.rpn] at heq2 ⊢
        grind
    case op operation =>
      cases ss; expose_names
      cases ts <;> simp at htslen; expose_names
      cases tail_1 <;> simp at htslen; expose_names
      have :
          ∃ ts', rpn_to_terms tail (.op operation head_1 head :: tail_1) = some ts'
            ∧ (Term.op operation head_1 head :: tail_1).reverse.flatMap (fun x => x.rpn) ++ tail
               = ts'.reverse.flatMap (fun x => x.rpn) := by
        apply (ih h); simp; omega
      obtain ⟨ts', heq1, heq2⟩ := this
      use ts'
      simp [rpn_to_terms]
      constructor
      · assumption
      · simp [Term.rpn] at heq2 ⊢
        grind
