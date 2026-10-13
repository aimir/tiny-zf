import TinyZF.Schemas

/-! # Well-formed formulas, total numeric decoding, and semantic interpretation

Every natural number is allowed as a source parameter. Invalid tags decode to
reflexive equality. Constructor laws hold even when their operands are invalid
codes. They are the bridge required to reason about garbage numeric inputs.
-/
namespace TinyZF.Source
open Cantor

/-- First-order formulas with natural-number variables and one membership relation. -/
inductive Formula where
  | eq (x y : Nat)
  | mem (x y : Nat)
  | imp (a b : Formula)
  | neg (a : Formula)
  | all (x : Nat) (a : Formula)
  deriving DecidableEq, Repr

/-- Encode syntax with the candidate's reversed binary payloads. -/
def Formula.code : Formula → Nat
  | .eq x y => weq x y
  | .mem x y => wel x y
  | .imp a b => wim a.code b.code
  | .neg a => wn a.code
  | .all x a => wal x a.code

/-- Positive constructor tags force smaller recursive payloads. -/
theorem payload_lt {n : Nat} (h : 0 < (unpair n).2) : (unpair n).1 < n := by
  have hp := left_lt (unpair n).1 (unpair n).2 h
  simpa using hp

/-- A total interpretation of all formula numbers; malformed tags are harmless defaults. -/
def decodeFormula (n : Nat) : Formula :=
  let p := (unpair n).1
  let t := (unpair n).2
  if t = 2 then .imp (decodeFormula (unpair p).2) (decodeFormula (unpair p).1)
  else if t = 3 then .neg (decodeFormula p)
  else if t = 4 then .all (unpair p).2 (decodeFormula (unpair p).1)
  else if t = 0 then .eq (unpair p).2 (unpair p).1
  else if t = 1 then .mem (unpair p).2 (unpair p).1
  else .eq 0 0
termination_by n
decreasing_by
  all_goals
    have hp : (unpair n).1 < n := payload_lt (by omega)
    have hs := unpair_le (unpair n).1
    omega

/-- Equality payloads decode in the source operand order. -/
@[simp] theorem decode_weq (x y : Nat) : decodeFormula (weq x y) = .eq x y := by
  rw [decodeFormula]
  simp [weq]

/-- Membership payloads decode in the source operand order. -/
@[simp] theorem decode_wel (x y : Nat) : decodeFormula (wel x y) = .mem x y := by
  rw [decodeFormula]
  simp [wel]

/-- Implication decoding works for arbitrary, possibly malformed, operand codes. -/
@[simp] theorem decode_wim (a b : Nat) :
    decodeFormula (wim a b) = .imp (decodeFormula a) (decodeFormula b) := by
  rw [decodeFormula]
  simp [wim]

/-- Negation decoding preserves arbitrary operands. -/
@[simp] theorem decode_wn (a : Nat) : decodeFormula (wn a) = .neg (decodeFormula a) := by
  rw [decodeFormula]
  simp [wn]

/-- Quantification decoding recovers its variable and arbitrary body. -/
@[simp] theorem decode_wal (x a : Nat) :
    decodeFormula (wal x a) = .all x (decodeFormula a) := by
  rw [decodeFormula]
  simp [wal]

/-- Decoding a well-formed formula is a left inverse of encoding. -/
@[simp] theorem decode_code (a : Formula) : decodeFormula a.code = a := by
  induction a <;> simp_all [Formula.code]

/-- The changed operand convention is injective on well-formed formulas. -/
theorem code_injective : Function.Injective Formula.code := by
  intro a b h
  simpa using congrArg decodeFormula h

/-- The default theorem has its expected well-formed meaning. -/
@[simp] theorem decode_zero : decodeFormula 0 = .eq 0 0 := decode_weq 0 0

/-- The literal halt-test value is precisely `v₀ ∈ v₀`. -/
@[simp] theorem decode_one : decodeFormula 1 = .mem 0 0 := decode_wel 0 0

/-- Ordinary first-order semantics; equality is actual equality on the domain. -/
def Formula.eval {α : Type} (membership : α → α → Prop) (env : Nat → α) : Formula → Prop
  | .eq x y => env x = env y
  | .mem x y => membership (env x) (env y)
  | .imp a b => a.eval membership env → b.eval membership env
  | .neg a => ¬ a.eval membership env
  | .all x a => ∀ v, a.eval membership (Function.update env x v)

/-- A source model satisfies all actual guarded, permuted, rewritten schema instances.
This does not assert existence of such a model or its equivalence to a ZF model. -/
def ModelsSource {α : Type} (membership : α → α → Prop) : Prop :=
  ∀ (k : Fin 15) (p1 p2 p3 : Nat) (env : Nat → α),
    (decodeFormula (schema k p1 p2 p3)).eval membership env

/-- Numeric derivations have ordinary first-order meaning in every source model.
The proof of this theorem is in `Interpretation`, after the numeric calculus. -/
def Valid {α : Type} (membership : α → α → Prop) (n : Nat) : Prop :=
  ∀ env, (decodeFormula n).eval membership env

end TinyZF.Source
