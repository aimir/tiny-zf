import TinyZF.Enumeration

/-! # Structured primitive register programs

This language exposes every increment and decrement. Its loops and branches
are control structure, not arithmetic oracles. The arithmetic library proves
finite executions in this language; a separate graph certificate must connect
these programs to the candidate's primitive instruction graph.
-/
namespace TinyZF.Interpreter

/-- All register contents are arbitrary natural numbers. -/
abbrev Values := Nat → Nat

/-- Structured control over primitive increment and zero-testing decrement.
 A break counts enclosing loops or blocks, starting at zero for the innermost. -/
inductive Code where
  | skip
  | inc (register : Nat)
  | seq (first second : Code)
  | ifDec (register : Nat) (positive zero : Code)
  | whileDec (register : Nat) (body : Code)
  | block (body : Code)
  | breakLoop (outer : Nat)
  | halt
  deriving DecidableEq

/-- The possible exits of a finite structured execution. -/
inductive Exit where
  | normal
  | breakLoop (outer : Nat)
  | halt
  deriving DecidableEq

/-- Finite execution, including early loop exit and halting. A positive test
 consumes one unit before executing its body. No instruction can inspect or
 update a register except the explicit increment and decrement rules. -/
inductive Run : Code → Values → Exit → Values → Prop where
  | skip (R) : Run .skip R .normal R
  | inc (r R) : Run (.inc r) R .normal (Function.update R r (R r+1))
  | seq {a b R S T x} : Run a R .normal S → Run b S x T → Run (.seq a b) R x T
  | escape {a b R S x} : Run a R x S → x ≠ .normal → Run (.seq a b) R x S
  | ifPositive {r a b R S x v} : R r = v+1 →
      Run a (Function.update R r v) x S → Run (.ifDec r a b) R x S
  | ifZero {r a b R S x} : R r = 0 → Run b R x S → Run (.ifDec r a b) R x S
  | whileZero {r body R} : R r = 0 → Run (.whileDec r body) R .normal R
  | whileNext {r body R S T x v} : R r = v+1 →
      Run body (Function.update R r v) .normal S →
      Run (.whileDec r body) S x T → Run (.whileDec r body) R x T
  | whileBreak {r body R S v} : R r = v+1 →
      Run body (Function.update R r v) (.breakLoop 0) S → Run (.whileDec r body) R .normal S
  | whileOuter {r body R S v k} : R r = v+1 →
      Run body (Function.update R r v) (.breakLoop (k+1)) S →
      Run (.whileDec r body) R (.breakLoop k) S
  | whileHalt {r body R S v} : R r = v+1 →
      Run body (Function.update R r v) .halt S → Run (.whileDec r body) R .halt S
  | blockNormal {body R S} : Run body R .normal S → Run (.block body) R .normal S
  | blockBreak {body R S} : Run body R (.breakLoop 0) S → Run (.block body) R .normal S
  | blockOuter {body R S k} : Run body R (.breakLoop (k+1)) S → Run (.block body) R (.breakLoop k) S
  | blockHalt {body R S} : Run body R .halt S → Run (.block body) R .halt S
  | breakLoop (k R) : Run (.breakLoop k) R (.breakLoop k) R
  | halt (R) : Run .halt R .halt R

/-- Compose a finite list of commands in order. The final skip is inert. -/
def sequence (codes : List Code) : Code := codes.foldr Code.seq .skip

/-- A loop whose body preserves its counter terminates after exactly the
 original counter many body executions. The invariant `post` states the
 complete final register file, including scratch and untouched registers. -/
theorem while_rule (r : Nat) (body : Code) (bodyResult post : Values → Values)
    (exec : ∀ R, Run body R .normal (bodyResult R))
    (preserves : ∀ R, bodyResult R r = R r)
    (zero : ∀ R, R r = 0 → post R = R)
    (positive : ∀ R v, R r = v+1 →
      post R = post (bodyResult (Function.update R r v))) :
    ∀ R, Run (.whileDec r body) R .normal (post R) := by
  have h : ∀ n R, R r = n → Run (.whileDec r body) R .normal (post R) := by
    intro n
    induction n with
    | zero =>
      intro R hr
      rw [zero R hr]
      exact .whileZero hr
    | succ n ih =>
      intro R hr
      rw [positive R n hr]
      exact .whileNext hr (exec _) (ih _ (by simp [preserves]))
  intro R
  exact h (R r) R rfl

/-- Counter induction with a register invariant. Each positive iteration
 supplies its actual body execution, preserves the invariant, and reduces the
 counter by one while preserving the claimed final result. -/
theorem while_invariant (r : Nat) (body : Code) (invariant : Values → Prop)
    (post : Values → Values)
    (zero : ∀ R, invariant R → R r = 0 → post R = R)
    (positive : ∀ R v, invariant R → R r = v+1 →
      ∃ S, Run body (Function.update R r v) .normal S ∧
        invariant S ∧ S r = v ∧ post R = post S) :
    ∀ R, invariant R → Run (.whileDec r body) R .normal (post R) := by
  have h : ∀ n R, invariant R → R r = n →
      Run (.whileDec r body) R .normal (post R) := by
    intro n
    induction n with
    | zero =>
      intro R hi hr
      rw [zero R hi hr]
      exact .whileZero hr
    | succ n ih =>
      intro R hi hr
      obtain ⟨S, run, inv, counter, postEq⟩ := positive R n hi hr
      rw [postEq]
      exact .whileNext hr run (ih S inv counter)
  intro R hi
  exact h (R r) R hi rfl

end TinyZF.Interpreter
