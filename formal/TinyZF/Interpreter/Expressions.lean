import TinyZF.Interpreter.Stack

/-! # Formula expressions compiled to primitive stack routines

A single structural induction proves every schema expression, including the
expanded Boolean rewrites. The expression data must still be tied to the fixed
`Source.schema` definitions, and their concrete instruction placements checked.
-/
namespace TinyZF.Interpreter.Expressions
open Cantor FormulaStack

/-- The three decoded proof parameters, at physical addresses five through seven. -/
def parameters (R : Values) : Fin 3 → Nat := fun i => R (5+i.val)

/-- Formula-stack changes preserve all decoded proof parameters. -/
theorem parameters_setStack (R : Values) (top stack : Nat) :
    parameters (setStack R top stack) = parameters R := by
  funext i
  simp [parameters, setStack, show 5+i.val ≠ 2 by omega, show 5+i.val ≠ 3 by omega]

/-- Replacing a stack leaves both scratch registers unchanged. -/
theorem scratch_setStack (R : Values) (top stack : Nat) (h : ScratchFree R) :
    ScratchFree (setStack R top stack) := by simpa [ScratchFree, setStack] using h

/-- Expression syntax exposes the unary and reversed binary Cantor constructors.
 All formulas in the fixed source schemas use only these and the three parameters. -/
inductive Expr where
  | parameter (index : Fin 3)
  | unary (tag : Nat) (operand : Expr)
  | binary (tag : Nat) (left right : Expr)
  deriving DecidableEq

/-- Pure numeric meaning of a schema expression. -/
def eval : Expr → (Fin 3 → Nat) → Nat
  | .parameter i, p => p i
  | .unary k e, p => pair (eval e p) k
  | .binary k a b, p => pair (pair (eval b p) (eval a p)) k

/-- Compilation uses only the already proved primitive-loop stack routines. -/
def emit : Expr → Code
  | .parameter i => FormulaStack.parameter (5+i.val)
  | .unary k e => .seq (emit e) (tag k)
  | .binary k a b => .seq (emit a) (.seq (emit b) (FormulaStack.binary k))

/-- Compiling any finite expression pushes exactly its value above the old
 caller stack, preserves all other registers, and restores scratch. -/
theorem emit_run (e : Expr) (R : Values) (scratch : ScratchFree R) :
    Run (emit e) R .normal (setStack R (eval e (parameters R)) (pair (R 2) (R 3))) := by
  induction e generalizing R with
  | parameter i =>
    exact parameter_run (5+i.val) (by omega) (by omega) (by have := i.isLt; omega)
      (by have := i.isLt; omega) R scratch
  | unary k e ih =>
    let V := setStack R (eval e (parameters R)) (pair (R 2) (R 3))
    have hv : ScratchFree V := scratch_setStack _ _ _ scratch
    have h := Run.seq (ih R scratch) (tag_run k V hv)
    convert h using 1
    · rfl
    · funext i
      by_cases h2 : i = 2 <;> by_cases h3 : i = 3 <;> simp_all [eval, V, setStack]
  | binary k a b iha ihb =>
    let V := setStack R (eval a (parameters R)) (pair (R 2) (R 3))
    have hv : ScratchFree V := scratch_setStack _ _ _ scratch
    have hp : parameters V = parameters R := parameters_setStack _ _ _
    have hb := ihb V hv
    rw [hp] at hb
    let W := setStack V (eval b (parameters R)) (pair (V 2) (V 3))
    have hw : ScratchFree W := scratch_setStack _ _ _ hv
    have h := Run.seq (iha R scratch) (Run.seq hb (binary_run k W hw))
    convert h using 1
    · rfl
    · funext i
      by_cases h2 : i = 2 <;> by_cases h3 : i = 3 <;> simp_all [eval, V, W, setStack]

end TinyZF.Interpreter.Expressions
