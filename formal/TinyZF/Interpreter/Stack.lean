import TinyZF.Interpreter.Decoder
import TinyZF.Source

/-! # Formula-stack routines implemented by primitive loops

The physical addresses are top=2, encoded stack=3, scratch1=8, scratch2=9.
Each contract preserves the complete register file except its stated stack
change, and restores both initially zero scratch registers. These routines
provide the formula-construction and clause-selection layer of the source
interpreter proof; their concrete graph placements remain separate.
-/
namespace TinyZF.Interpreter.FormulaStack
open Cantor

/-- Replace just the formula top and encoded stack, preserving all other registers. -/
def setStack (R : Values) (top stack : Nat) : Values :=
  Function.update (Function.update R 2 top) 3 stack

/-- Stack routines share two cleared scratch registers. -/
def ScratchFree (R : Values) : Prop := R 8 = 0 ∧ R 9 = 0

/-- The zero pair is the first point of the diagonal walk. -/
private theorem pair_zero_zero : pair 0 0 = 0 := rfl

/-- Push the old top onto the encoded stack, leaving a zero top. -/
def push : Code :=
  .seq (move 3 [8]) (.seq (pairCode 9 2 8) (move 9 [3]))

/-- The shared push implementation realizes exactly Cantor stack encoding. -/
theorem push_run (R : Values) (scratch : ScratchFree R) :
    Run push R .normal (setStack R 0 (pair (R 2) (R 3))) := by
  let V := Function.update (Function.update R 3 0) 8 (R 8+R 3)
  let W := Function.update (Function.update (Function.update V 2 0) 8 0)
    9 (V 9+pair (V 2) (V 8))
  have h := Run.seq (move_one_run 3 8 (by decide) R)
    (Run.seq (pair_run 9 2 8 (by decide) (by decide) (by decide) V)
      (move_one_run 9 3 (by decide) W))
  convert h using 1
  · rfl
  · funext i
    rcases scratch with ⟨h8,h9⟩
    by_cases h2 : i = 2 <;> by_cases h3 : i = 3 <;>
      by_cases hi8 : i = 8 <;> by_cases hi9 : i = 9 <;>
      simp_all [setStack, V, W]

/-- Copy a named parameter onto the formula stack, restoring the parameter. -/
def parameter (r : Nat) : Code :=
  .seq push (.seq (move r [8,2]) (move 8 [r]))

/-- A parameter push preserves the old stack under its new top and restores
 every parameter and scratch register. -/
theorem parameter_run (r : Nat) (h2 : r ≠ 2) (h3 : r ≠ 3) (h8 : r ≠ 8) (h9 : r ≠ 9)
    (R : Values) (scratch : ScratchFree R) :
    Run (parameter r) R .normal (setStack R (R r) (pair (R 2) (R 3))) := by
  let V := setStack R 0 (pair (R 2) (R 3))
  let W := transferred r [8,2] V
  have h := Run.seq (push_run R scratch)
    (Run.seq (move_run r [8,2] (by simp [h8,h2]) V)
      (move_one_run 8 r (Ne.symm h8) W))
  convert h using 1
  · rfl
  · funext i
    rcases scratch with ⟨hs8,hs9⟩
    by_cases hi : i = r <;> by_cases hi2 : i = 2 <;> by_cases hi3 : i = 3 <;>
      by_cases hi8 : i = 8 <;> by_cases hi9 : i = 9 <;>
      simp_all [V, W, setStack, transferred, List.count_cons] <;> omega

/-- Pop the first operand and construct the candidate's reversed binary payload. -/
def cons : Code :=
  .seq (unpairCode 3 8 9) (.seq (move 9 [3])
    (.seq (pairCode 9 2 8) (move 9 [2])))

/-- Payload construction pops exactly one stack element, including the
 zero-underflow case, and restores both scratch registers. -/
theorem cons_run (R : Values) (scratch : ScratchFree R) :
    Run cons R .normal
      (setStack R (pair (R 2) (unpair (R 3)).1) (unpair (R 3)).2) := by
  let V := unpaired 3 8 9 R
  let W := Function.update (Function.update V 9 0) 3 (V 3+V 9)
  let X := Function.update (Function.update (Function.update W 2 0) 8 0)
    9 (W 9+pair (W 2) (W 8))
  have h := Run.seq (unpair_run 3 8 9 (by decide) (by decide) (by decide) R)
    (Run.seq (move_one_run 9 3 (by decide) V)
      (Run.seq (pair_run 9 2 8 (by decide) (by decide) (by decide) W)
        (move_one_run 9 2 (by decide) X)))
  convert h using 1
  · rfl
  · funext i
    rcases scratch with ⟨h8,h9⟩
    by_cases h2 : i = 2 <;> by_cases h3 : i = 3 <;>
      by_cases hi8 : i = 8 <;> by_cases hi9 : i = 9 <;>
      simp_all [setStack, V, W, X, unpaired, pair_zero_zero]

/-- Add a constructor tag using the shared pairing routine. -/
def tag (k : Nat) : Code :=
  .seq (increments (List.replicate k 8)) (.seq (pairCode 9 2 8) (move 9 [2]))

/-- Tagging preserves the encoded stack and adds exactly the specified outer
 Cantor tag to the old top. -/
theorem tag_run (k : Nat) (R : Values) (scratch : ScratchFree R) :
    Run (tag k) R .normal (Function.update R 2 (pair (R 2) k)) := by
  let V := addCounts (List.replicate k 8) R
  let W := Function.update (Function.update (Function.update V 2 0) 8 0)
    9 (V 9+pair (V 2) (V 8))
  have h := Run.seq (increments_run (List.replicate k 8) R)
    (Run.seq (pair_run 9 2 8 (by decide) (by decide) (by decide) V)
      (move_one_run 9 2 (by decide) W))
  convert h using 1
  · rfl
  · funext i
    rcases scratch with ⟨h8,h9⟩
    by_cases h2 : i = 2 <;> by_cases hi8 : i = 8 <;> by_cases hi9 : i = 9 <;>
      simp_all [V, W, addCounts, List.count_replicate] <;> omega

/-- A binary constructor combines the top two operands and adds its tag. -/
def binary (k : Nat) : Code := .seq cons (tag k)

/-- The constructor uses the candidate's reversed payload convention for
 every tag, including implication and universal quantification. -/
theorem binary_run (k : Nat) (R : Values) (scratch : ScratchFree R) :
    Run (binary k) R .normal
      (setStack R (pair (pair (R 2) (unpair (R 3)).1) k) (unpair (R 3)).2) := by
  let V := setStack R (pair (R 2) (unpair (R 3)).1) (unpair (R 3)).2
  have hv : ScratchFree V := by simpa [V, ScratchFree, setStack] using scratch
  have h := Run.seq (cons_run R scratch) (tag_run k V hv)
  convert h using 1
  · rfl
  · funext i
    by_cases h2 : i = 2 <;> by_cases h3 : i = 3 <;> simp_all [V, setStack]

/-- Pop a saved old top. A positive selector keeps the newly computed top and
 decrements the selector; a zero selector restores the saved top instead. -/
def select : Code :=
  .seq (unpairCode 3 8 9) (.seq (move 9 [3])
    (.seq (.ifDec 4 .skip (.seq (clear 2) (move 8 [2]))) (clear 8)))

/-- Exact postcondition of one clause-selection step. -/
def selected (R : Values) : Values :=
  Function.update (setStack R (if R 4 = 0 then (unpair (R 3)).1 else R 2)
    (unpair (R 3)).2) 4 (R 4-1)

/-- Selection restores scratch, pops exactly one saved top, and implements
 the saturating selector used by the full sequence of source clauses. -/
theorem select_run (R : Values) (scratch : ScratchFree R) :
    Run select R .normal (selected R) := by
  let V := unpaired 3 8 9 R
  let W := Function.update (Function.update V 9 0) 3 (V 3+V 9)
  have first := unpair_run 3 8 9 (by decide) (by decide) (by decide) R
  have second := move_one_run 9 3 (by decide) V
  cases h4 : R 4 with
  | zero =>
    let X := Function.update W 2 0
    let Y := Function.update (Function.update X 8 0) 2 (X 2+X 8)
    have choice : Run (.ifDec 4 .skip (.seq (clear 2) (move 8 [2]))) W .normal Y :=
      .ifZero (by simp [W, V, unpaired, h4])
        (.seq (clear_run 2 W) (move_one_run 8 2 (by decide) X))
    have h : Run select R .normal (Function.update Y 8 0) :=
      .seq first (.seq second (.seq choice (clear_run 8 Y)))
    convert h using 1
    funext i
    rcases scratch with ⟨h8,h9⟩
    by_cases h2 : i = 2 <;> by_cases h3 : i = 3 <;> by_cases hi4 : i = 4 <;>
      by_cases hi8 : i = 8 <;> by_cases hi9 : i = 9 <;>
      simp_all [selected, setStack, V, W, X, Y, unpaired, pair_zero_zero]
  | succ v =>
    let U := Function.update W 4 v
    have choice : Run (.ifDec 4 .skip (.seq (clear 2) (move 8 [2]))) W .normal U :=
      .ifPositive (by simp [W, V, unpaired, h4]) (.skip U)
    have h : Run select R .normal (Function.update U 8 0) :=
      .seq first (.seq second (.seq choice (clear_run 8 U)))
    convert h using 1
    funext i
    rcases scratch with ⟨h8,h9⟩
    by_cases h2 : i = 2 <;> by_cases h3 : i = 3 <;> by_cases hi4 : i = 4 <;>
      by_cases hi8 : i = 8 <;> by_cases hi9 : i = 9 <;>
      simp_all [selected, setStack, V, W, U, unpaired, pair_zero_zero]

/-- Pop a theorem into a parameter only when the current selector is one.
 The two destructive tests restore the selector on every positive branch. -/
def takeParameter (r : Nat) : Code :=
  .ifDec 4
    (.ifDec 4 (.seq (.inc 4) (.inc 4))
      (.seq (.inc 4) (.seq (unpairCode 3 8 9) (.seq (move 9 [3])
        (.seq (clear r) (move 8 [r]))))))
    .skip

/-- Conditional premise popping implements the inference-rule stack access:
 only the currently selected clause consumes a theorem, and the selector is
 preserved. The parameter may be any location disjoint from the working set. -/
theorem takeParameter_run (r : Nat) (h3 : r ≠ 3) (h4r : r ≠ 4)
    (h8r : r ≠ 8) (h9r : r ≠ 9) (R : Values) (scratch : ScratchFree R) :
    Run (takeParameter r) R .normal
      (if R 4 = 1 then Function.update (Function.update R 3 (unpair (R 3)).2)
        r (unpair (R 3)).1 else R) := by
  cases h4 : R 4 with
  | zero =>
    have h : Run (takeParameter r) R .normal R := .ifZero h4 (.skip R)
    simpa [h4] using h
  | succ v =>
    cases v with
    | zero =>
      let U := Function.update R 4 0
      have restore : Run (.inc 4) U .normal R := by
        convert Run.inc 4 U using 1
        funext i
        by_cases hi : i = 4 <;> simp [U, hi, h4]
      let V := unpaired 3 8 9 R
      let W := Function.update (Function.update V 9 0) 3 (V 3+V 9)
      let X := Function.update W r 0
      let Y := Function.update (Function.update X 8 0) r (X r+X 8)
      have hp := Run.seq (unpair_run 3 8 9 (by decide) (by decide) (by decide) R)
        (Run.seq (move_one_run 9 3 (by decide) V)
          (Run.seq (clear_run r W) (move_one_run 8 r (Ne.symm h8r) X)))
      have h : Run (takeParameter r) R .normal Y :=
        .ifPositive h4 (.ifZero (by simp [U]) (.seq restore hp))
      convert h using 1
      funext i
      rcases scratch with ⟨hs8,hs9⟩
      by_cases hi : i = r <;> by_cases hi3 : i = 3 <;> by_cases hi4 : i = 4 <;>
        by_cases hi8 : i = 8 <;> by_cases hi9 : i = 9 <;>
        simp_all [U, V, W, X, Y, unpaired, pair_zero_zero, Ne.symm h3,
          Ne.symm h4r, Ne.symm h8r, Ne.symm h9r] <;> omega
    | succ v =>
      let U := Function.update R 4 (v+1)
      let V := Function.update U 4 v
      let W := Function.update V 4 (V 4+1)
      have restore : Run (.seq (.inc 4) (.inc 4)) V .normal R := by
        convert Run.seq (Run.inc 4 V) (Run.inc 4 W) using 1
        funext i
        by_cases hi : i = 4 <;> simp [U, V, W, hi, h4]
      have h : Run (takeParameter r) R .normal R :=
        .ifPositive h4 (.ifPositive (by simp [U]) restore)
      simpa only [show v+1+1 ≠ 1 by omega, ite_false] using h

/-- Compare two parameters using the shared scratch and zero formula-top
 registers, incrementing the first parameter exactly when their values agree. -/
def safety (a b : Nat) : Code :=
  .seq (copyKeep a 8 9) (.seq (copyKeep b 8 2) (ifEqual 9 2 (.inc a)))

/-- The primitive guard realizes `Source.safe`, restoring all three working
 registers. Its parameter addresses must be distinct from those work locations. -/
theorem safety_run (a b : Nat) (hab : a ≠ b)
    (ha2 : a ≠ 2) (ha8 : a ≠ 8) (ha9 : a ≠ 9)
    (hb2 : b ≠ 2) (hb8 : b ≠ 8) (hb9 : b ≠ 9)
    (R : Values) (scratch : ScratchFree R) (topZero : R 2 = 0) :
    Run (safety a b) R .normal (Function.update R a (Source.safe (R a) (R b))) := by
  let V := Function.update R 9 (R 9+R a)
  let W := Function.update V 2 (V 2+V b)
  let C := Function.update (Function.update W 9 0) 2 0
  have second := copyKeep_run b 8 2 hb8 hb2 (by decide) V (by simp [V, scratch.1])
  have choice := ifEqual_run 9 2 (by decide) (.inc a) W
    (Function.update C a (C a+1)) (Run.inc a C)
  have h := Run.seq (copyKeep_run a 8 9 ha8 ha9 (by decide) R scratch.1)
    (Run.seq second choice)
  convert h using 1
  · rfl
  · funext i
    rcases scratch with ⟨h8,h9⟩
    by_cases he : R a = R b <;> by_cases hi : i = a <;>
      by_cases hi2 : i = 2 <;> by_cases hi8 : i = 8 <;> by_cases hi9 : i = 9 <;>
      simp_all [V, W, C, Source.safe, Ne.symm ha2, Ne.symm ha8, Ne.symm ha9,
        Ne.symm hb2, Ne.symm hb8, Ne.symm hb9] <;> omega

end TinyZF.Interpreter.FormulaStack
