import TinyZF.Interpreter.SchemaCode

/-! # Primitive implementations of all source clauses

These contracts cover axiom construction, both inference rules, and the
protected-parameter guards. They describe the entire physical register file;
concrete placements in the finite instruction graph are checked separately.
-/
set_option maxHeartbeats 2000000

namespace TinyZF.Interpreter.Clauses
open Cantor FormulaStack Expressions

/-- A formula expression followed by the common saturating selector. -/
def expressionClause (e : Expr) : Code := .seq (emit e) select

/-- A clause replaces the theorem only while the selector remains positive.
 All parameters, the encoded stack, and scratch are preserved. -/
def expressionAfter (e : Expr) (R : Values) : Values :=
  Function.update (Function.update R 2
    (if R 4 = 0 then R 2 else eval e (parameters R))) 4 (R 4-1)

/-- Any expression clause has exactly the source selector behavior. -/
theorem expressionClause_run (e : Expr) (R : Values) (scratch : ScratchFree R) :
    Run (expressionClause e) R .normal (expressionAfter e R) := by
  let V := setStack R (eval e (parameters R)) (pair (R 2) (R 3))
  have h := Run.seq (emit_run e R scratch) (select_run V (scratch_setStack _ _ _ scratch))
  convert h using 1
  · rfl
  · funext i
    by_cases h2 : i = 2 <;> by_cases h3 : i = 3 <;> by_cases h4 : i = 4 <;>
      simp_all [expressionAfter, V, selected, setStack]

/-- Full effect of the conditional premise-pop routine. -/
def taken (r : Nat) (R : Values) : Values :=
  if R 4 = 1 then Function.update (Function.update R 3 (unpair (R 3)).2)
    r (unpair (R 3)).1 else R

/-- Conditional premise popping restores both scratch registers. -/
theorem taken_scratch (r : Nat) (h8 : r ≠ 8) (h9 : r ≠ 9)
    (R : Values) (scratch : ScratchFree R) : ScratchFree (taken r R) := by
  unfold taken
  split_ifs <;> simpa [ScratchFree, Ne.symm h8, Ne.symm h9] using scratch

/-- Generalization reads its premise only if selected, then constructs and selects. -/
def generalize : Code :=
  .seq (takeParameter 7) (expressionClause (.binary 4 (.parameter 0) (.parameter 2)))

/-- The exact register effect of generalization, including unselected clauses. -/
def generalized (R : Values) : Values :=
  expressionAfter (.binary 4 (.parameter 0) (.parameter 2)) (taken 7 R)

/-- The primitive generalization routine implements universal quantification. -/
theorem generalize_run (R : Values) (scratch : ScratchFree R) :
    Run generalize R .normal (generalized R) :=
  .seq (takeParameter_run 7 (by decide) (by decide) (by decide) (by decide) R scratch)
    (expressionClause_run _ (taken 7 R) (taken_scratch 7 (by decide) (by decide) R scratch))

/-- Compare the formula top to the major premise, returning the candidate
 conclusion in register five on equality and the harmless default otherwise. -/
def detachCompare : Code :=
  .seq (move 2 [9]) (.seq (copyKeep 6 8 2) (ifEqual 9 2 (copyKeep 5 8 2)))

/-- Comparison consumes its work registers but preserves parameters and stack. -/
theorem detachCompare_run (R : Values) (scratch : ScratchFree R) :
    Run detachCompare R .normal (Function.update R 2 (if R 2 = R 6 then R 5 else 0)) := by
  let V := Function.update (Function.update R 2 0) 9 (R 9+R 2)
  let W := Function.update V 2 (V 2+V 6)
  let C := Function.update (Function.update W 9 0) 2 0
  have body := copyKeep_run 5 8 2 (by decide) (by decide) (by decide) C
    (by simp [C, W, V, scratch.1])
  have choice := ifEqual_run 9 2 (by decide) (copyKeep 5 8 2) W _ body
  have h := Run.seq (move_one_run 2 9 (by decide) R)
    (Run.seq (copyKeep_run 6 8 2 (by decide) (by decide) (by decide) V
      (by simp [V, scratch.1])) choice)
  convert h using 1
  · rfl
  · funext i
    rcases scratch with ⟨h8,h9⟩
    by_cases he : R 2 = R 6 <;> by_cases h2 : i = 2 <;>
      by_cases hi8 : i = 8 <;> by_cases hi9 : i = 9 <;> simp_all [V, W, C]

/-- Pop both premises only for the selected detachment clause, construct the
 expected implication, compare it, then run the common selector. -/
def detach : Code :=
  .seq (takeParameter 7) (.seq (takeParameter 6)
    (.seq (emit (.binary 2 (.parameter 2) (.parameter 0)))
      (.seq detachCompare select)))

/-- Exact detachment effect, retaining the conditional premise changes. -/
def detached (R : Values) : Values :=
  let U := taken 6 (taken 7 R)
  Function.update (Function.update U 2
    (if R 4 = 0 then R 2 else if Source.wim (U 7) (U 5) = U 6 then U 5 else 0))
    4 (R 4-1)

/-- The primitive detachment routine implements precisely the numeric
 implication check, including failed checks and zero-padded stack underflow. -/
theorem detach_run (R : Values) (scratch : ScratchFree R) :
    Run detach R .normal (detached R) := by
  let T := taken 7 R
  have ht : ScratchFree T := taken_scratch 7 (by decide) (by decide) R scratch
  let U := taken 6 T
  have hu : ScratchFree U := taken_scratch 6 (by decide) (by decide) T ht
  let e : Expr := .binary 2 (.parameter 2) (.parameter 0)
  let V := setStack U (eval e (parameters U)) (pair (U 2) (U 3))
  have hv : ScratchFree V := scratch_setStack _ _ _ hu
  let W := Function.update V 2 (if V 2 = V 6 then V 5 else 0)
  have hw : ScratchFree W := by simpa [W, ScratchFree] using hv
  have h := Run.seq
    (takeParameter_run 7 (by decide) (by decide) (by decide) (by decide) R scratch)
    (Run.seq (takeParameter_run 6 (by decide) (by decide) (by decide) (by decide) T ht)
      (Run.seq (emit_run e U hu) (Run.seq (detachCompare_run V hv) (select_run W hw))))
  convert h using 1
  · rfl
  · funext i
    by_cases h4 : R 4 = 1 <;> by_cases h2 : i = 2 <;> by_cases h3 : i = 3 <;>
      by_cases hi4 : i = 4 <;> by_cases h6 : i = 6 <;> by_cases h7 : i = 7 <;>
      simp_all [detached, T, U, V, W, e, selected, setStack, taken, eval, parameters, Source.wim]

/-- Both protected guards run with a temporarily saved formula top. -/
def protect : Code :=
  .seq push (.seq (safety 5 6) (.seq (safety 7 6)
    (.seq (unpairCode 3 8 9) (.seq (move 9 [3]) (move 8 [2])))))

/-- Guarded parameters, with all persistent theorem data preserved. -/
def guarded (R : Values) : Values :=
  Function.update (Function.update R 5 (Source.safe (R 5) (R 6)))
    7 (Source.safe (R 7) (R 6))

/-- The actual primitive guard prefix preserves both theorem-stack registers
 and increments exactly those two parameters equal to the bound variable. -/
theorem protect_run (R : Values) (scratch : ScratchFree R) :
    Run protect R .normal (guarded R) := by
  let V := setStack R 0 (pair (R 2) (R 3))
  have hv : ScratchFree V := scratch_setStack _ _ _ scratch
  let W := Function.update V 5 (Source.safe (V 5) (V 6))
  have hw : ScratchFree W := by simpa [W, ScratchFree] using hv
  let X := Function.update W 7 (Source.safe (W 7) (W 6))
  let Y := unpaired 3 8 9 X
  let Z := Function.update (Function.update Y 9 0) 3 (Y 3+Y 9)
  have h := Run.seq (push_run R scratch)
    (Run.seq (safety_run 5 6 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) V hv (by simp [V, setStack]))
      (Run.seq (safety_run 7 6 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) W hw (by simp [W, V, setStack]))
        (Run.seq (unpair_run 3 8 9 (by decide) (by decide) (by decide) X)
          (Run.seq (move_one_run 9 3 (by decide) Y) (move_one_run 8 2 (by decide) Z)))))
  convert h using 1
  · rfl
  · funext i
    rcases scratch with ⟨h8,h9⟩
    by_cases h2 : i = 2 <;> by_cases h3 : i = 3 <;> by_cases h5 : i = 5 <;>
      by_cases h7 : i = 7 <;> by_cases hi8 : i = 8 <;> by_cases hi9 : i = 9 <;>
      simp_all [guarded, V, W, X, Y, Z, setStack, unpaired, show pair 0 0 = 0 from rfl]

end TinyZF.Interpreter.Clauses
