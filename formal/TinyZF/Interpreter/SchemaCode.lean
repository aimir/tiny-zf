import TinyZF.Interpreter.Expressions

/-! # The fixed schema expressions and their independent specification

Generated expression trees describe primitive stack code. The theorem
below checks their values against the existing source schema definitions;
the generator is not a correctness assumption. -/
namespace TinyZF.Interpreter.SchemaCode
open Expressions

/-- Stack expression for each of the fifteen fixed schema clauses. -/
def expression (k : Fin 15) : Expr :=
  match k.val with
  | 0 => (.binary 2 (.binary 2 (.parameter 2) (.parameter 1)) (.binary 2 (.binary 2 (.parameter 1) (.parameter 0)) (.binary 2 (.parameter 2) (.parameter 0)))) -- B1
  | 1 => (.binary 2 (.binary 2 (.unary 3 (.parameter 0)) (.parameter 0)) (.parameter 0)) -- B2
  | 2 => (.binary 2 (.parameter 1) (.binary 2 (.unary 3 (.parameter 1)) (.parameter 0))) -- B3
  | 3 => (.binary 2 (.binary 4 (.parameter 1) (.binary 2 (.parameter 0) (.parameter 2))) (.binary 2 (.binary 4 (.parameter 1) (.parameter 0)) (.binary 4 (.parameter 1) (.parameter 2)))) -- B4
  | 4 => (.binary 2 (.binary 4 (.parameter 1) (.binary 4 (.parameter 0) (.parameter 2))) (.binary 4 (.parameter 0) (.binary 4 (.parameter 1) (.parameter 2)))) -- B6b
  | 5 => (.binary 2 (.unary 3 (.binary 4 (.parameter 1) (.unary 3 (.binary 4 (.parameter 1) (.parameter 0))))) (.parameter 0)) -- B6c
  | 6 => (.unary 3 (.binary 4 (.parameter 0) (.unary 3 (.binary 0 (.parameter 0) (.parameter 1))))) -- B7
  | 7 => (.binary 2 (.binary 0 (.parameter 0) (.parameter 2)) (.binary 2 (.binary 0 (.parameter 0) (.parameter 1)) (.binary 0 (.parameter 2) (.parameter 1)))) -- B8a
  | 8 => (.binary 2 (.binary 0 (.parameter 0) (.parameter 1)) (.binary 2 (.binary 1 (.parameter 0) (.parameter 2)) (.binary 1 (.parameter 1) (.parameter 2)))) -- B8b
  | 9 => (.binary 2 (.binary 0 (.parameter 0) (.parameter 2)) (.binary 2 (.binary 1 (.parameter 1) (.parameter 0)) (.binary 1 (.parameter 1) (.parameter 2)))) -- B8c
  | 10 => (.unary 3 (.binary 4 (.parameter 2) (.unary 3 (.binary 4 (.parameter 1) (.binary 2 (.binary 4 (.parameter 2) (.binary 2 (.binary 1 (.parameter 2) (.parameter 1)) (.binary 1 (.parameter 2) (.parameter 0)))) (.binary 1 (.parameter 1) (.parameter 2))))))) -- POW
  | 11 => (.unary 3 (.binary 4 (.parameter 2) (.unary 3 (.binary 4 (.parameter 1) (.binary 2 (.unary 3 (.binary 4 (.parameter 2) (.binary 2 (.binary 1 (.parameter 1) (.parameter 2)) (.unary 3 (.binary 1 (.parameter 2) (.parameter 0)))))) (.binary 1 (.parameter 1) (.parameter 2))))))) -- UNI
  | 12 => (.unary 3 (.binary 4 (.parameter 2) (.binary 2 (.binary 4 (.parameter 1) (.unary 3 (.binary 2 (.binary 2 (.binary 1 (.parameter 1) (.parameter 2)) (.unary 3 (.binary 4 (.parameter 0) (.unary 3 (.parameter 2))))) (.unary 3 (.binary 2 (.binary 1 (.parameter 1) (.parameter 0)) (.binary 2 (.unary 3 (.binary 4 (.parameter 0) (.unary 3 (.parameter 2)))) (.binary 1 (.parameter 1) (.parameter 2)))))))) (.unary 3 (.binary 4 (.parameter 0) (.binary 2 (.unary 3 (.binary 4 (.parameter 1) (.binary 2 (.parameter 2) (.unary 3 (.binary 4 (.parameter 1) (.binary 2 (.parameter 2) (.unary 3 (.binary 1 (.parameter 1) (.parameter 2))))))))) (.unary 3 (.binary 1 (.parameter 0) (.parameter 2))))))))) -- ICS
  | 13 => (.binary 2 (.binary 0 (.parameter 0) (.parameter 2)) (.binary 4 (.parameter 1) (.binary 0 (.parameter 0) (.parameter 2)))) -- B6a1
  | _ => (.binary 2 (.binary 1 (.parameter 0) (.parameter 2)) (.binary 4 (.parameter 1) (.binary 1 (.parameter 0) (.parameter 2)))) -- B6a2

/-- Parameters after the actual protected-phase guards. -/
def guarded (k : Fin 15) (p : Fin 3 → Nat) : Fin 3 → Nat :=
  if k.val < 10 then p else fun i =>
    if i = 1 then p 1 else Source.safe (p i) (p 1)

/-- Every generated expression has exactly the independently specified
 schema value, including protected guards and the selected rewrites. -/
theorem expression_value (k : Fin 15) (p : Fin 3 → Nat) :
    eval (expression k) (guarded k p) = Source.schema k (p 0) (p 1) (p 2) := by
  fin_cases k <;> rfl

end TinyZF.Interpreter.SchemaCode
