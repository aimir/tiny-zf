import TinyZF.Interpreter.Structured

/-! # Arithmetic implemented using only primitive register instructions

These contracts describe entire register files, including consumed operands
and scratch storage. Pairing and unpairing are proved by loop invariants, not
introduced as primitive instructions. Connecting these structured fragments to
the concrete candidate graph is a separate certificate obligation.
-/
namespace TinyZF.Interpreter
open Cantor

/-- Increment each listed destination once, in order. Duplicates are allowed. -/
def increments (destinations : List Nat) : Code :=
  sequence (destinations.map Code.inc)

/-- Complete effect of those increments on every register. -/
def addCounts (destinations : List Nat) (R : Values) : Values :=
  fun i => R i + destinations.count i

/-- The increment list has its stated effect for arbitrary register values. -/
theorem increments_run (destinations : List Nat) (R : Values) :
    Run (increments destinations) R .normal (addCounts destinations R) := by
  induction destinations generalizing R with
  | nil =>
    have he : addCounts [] R = R := by funext i; simp [addCounts]
    rw [he]
    exact .skip R
  | cons a rest ih =>
    have h := Run.seq (Run.inc a R) (ih (Function.update R a (R a+1)))
    convert h using 1
    · rfl
    · funext i
      by_cases hi : i = a
      · subst i; simp [addCounts, List.count_cons]; omega
      · simp [addCounts, List.count_cons, hi, Ne.symm hi]

/-- Consume a source register, copying each consumed unit to every destination.
 This one primitive loop implements moves, destructive copies, and clearing. -/
def move (source : Nat) (destinations : List Nat) : Code :=
  .whileDec source (increments destinations)

/-- Exact full-file postcondition of a destructive copy. -/
def transferred (source : Nat) (destinations : List Nat) (R : Values) : Values :=
  fun i => if i = source then 0 else R i + destinations.count i * R source

/-- The copying loop terminates on all natural inputs, consumes its source,
 and adds the original source value to every listed destination. -/
theorem move_run (source : Nat) (destinations : List Nat)
    (distinct : source ∉ destinations) (R : Values) :
    Run (move source destinations) R .normal (transferred source destinations R) := by
  have hc : destinations.count source = 0 := List.count_eq_zero.mpr distinct
  apply while_rule source (increments destinations) (addCounts destinations)
    (transferred source destinations) (increments_run destinations)
  · intro V
    simp [addCounts, hc]
  · intro V hv
    funext i
    by_cases hi : i = source <;> simp [transferred, hi, hv]
  · intro V v hv
    funext i
    by_cases hi : i = source
    · simp [transferred, hi]
    · simp [transferred, addCounts, hi, hc, hv, Nat.mul_add]
      omega

/-- Clearing is the destructive-copy loop with no destinations. -/
def clear (r : Nat) : Code := move r []

/-- Clearing really executes primitive decrements, leaving all other values
 unchanged. The input value is unbounded. -/
theorem clear_run (r : Nat) (R : Values) :
    Run (clear r) R .normal (Function.update R r 0) := by
  change Run (move r []) R .normal _
  have h := move_run r [] (by simp) R
  convert h using 1
  funext i
  by_cases hi : i = r <;> simp [transferred, hi]

/-- A one-destination copy has the usual two-update postcondition. -/
theorem move_one_run (r s : Nat) (h : r ≠ s) (R : Values) :
    Run (move r [s]) R .normal
      (Function.update (Function.update R r 0) s (R s+R r)) := by
  have hh := move_run r [s] (by simpa using h) R
  convert hh using 1
  funext i
  by_cases hr : i = r
  · simp [transferred, hr, h, Ne.symm h, List.count_cons]
  · by_cases hs : i = s
    · subst i; simp [transferred, h, Ne.symm h, List.count_cons]
    · simp [transferred, hr, hs, Ne.symm hs, List.count_cons]

/-- Copy into an additive destination and restore the source through a zero
 temporary. This is the shared copy pattern used by parameters and guards. -/
def copyKeep (source temporary destination : Nat) : Code :=
  .seq (move source [temporary,destination]) (move temporary [source])

/-- Shared copying preserves its source and cleared temporary, and adds the
 original source to its destination while preserving every other register. -/
theorem copyKeep_run (source temporary destination : Nat)
    (hst : source ≠ temporary) (hsd : source ≠ destination) (htd : temporary ≠ destination)
    (R : Values) (zero : R temporary = 0) :
    Run (copyKeep source temporary destination) R .normal
      (Function.update R destination (R destination+R source)) := by
  let V := transferred source [temporary,destination] R
  have h := Run.seq (move_run source [temporary,destination] (by simp [hst,hsd]) R)
    (move_one_run temporary source (Ne.symm hst) V)
  convert h using 1
  · rfl
  · funext i
    by_cases hs : i = source <;> by_cases ht : i = temporary <;> by_cases hd : i = destination <;>
      simp_all [V, transferred, List.count_cons, Ne.symm hst, Ne.symm hsd, Ne.symm htd] <;> omega

/-- One diagonal-walk step used inside the unpairing loop. -/
def unpairBody (a b : Nat) : Code :=
  .seq (.inc a) (.ifDec b .skip (move a [b]))

/-- Exact register effect of one diagonal-walk step. -/
def diagonalStep (a b : Nat) (R : Values) : Values :=
  let next := advance (R a, R b)
  Function.update (Function.update R a next.1) b next.2

/-- The unpairing body implements the mathematical diagonal successor,
 including the transfer that starts a new diagonal. -/
theorem unpairBody_run (a b : Nat) (hab : a ≠ b) (R : Values) :
    Run (unpairBody a b) R .normal (diagonalStep a b R) := by
  cases hb : R b with
  | zero =>
    have h := Run.seq (Run.inc a R)
      (Run.ifZero (r := b) (a := .skip) (by simp [hab, hb, Ne.symm hab])
        (move_one_run a b hab (Function.update R a (R a+1))))
    convert h using 1
    · rfl
    · funext i
      by_cases ha : i = a
      · subst i; simp [diagonalStep, advance, hb, hab, Ne.symm hab]
      · by_cases hi : i = b
        · subst i; simp [diagonalStep, advance, hb, hab, Ne.symm hab]
        · simp [diagonalStep, advance, hb, ha, hi]
  | succ v =>
    have h := Run.seq (Run.inc a R)
      (Run.ifPositive (r := b) (b := move a [b]) (v := v)
        (by simp [hab, hb, Ne.symm hab])
        (Run.skip (Function.update (Function.update R a (R a+1)) b v)))
    convert h using 1
    · rfl
    · simp [diagonalStep, advance, hb]

/-- Advancing a diagonal position increases its paired code by exactly one. -/
theorem advance_pair (a b : Nat) :
    pair (advance (a,b)).1 (advance (a,b)).2 = pair a b + 1 := by
  cases b with
  | zero => simp [advance, pair, tri]; omega
  | succ b =>
    simp only [advance, pair]
    rw [show a+1+b = a+(b+1) by omega]
    omega

/-- Primitive unpairing consumes its input and walks from the original output
 pair, so the contract also covers nonzero output registers. -/
def unpairCode (input a b : Nat) : Code := .whileDec input (unpairBody a b)

/-- Full-file result of unpairing, with all nonparticipants preserved. -/
def unpaired (input a b : Nat) (R : Values) : Values :=
  let value := unpair (pair (R a) (R b) + R input)
  Function.update (Function.update (Function.update R input 0) a value.1) b value.2

/-- The complete unpairing loop satisfies its arithmetic contract for
 arbitrary input and output values; its three registers must be distinct. -/
theorem unpair_run (input a b : Nat) (hia : input ≠ a) (hib : input ≠ b)
    (hab : a ≠ b) (R : Values) :
    Run (unpairCode input a b) R .normal (unpaired input a b R) := by
  apply while_rule input (unpairBody a b) (diagonalStep a b)
    (unpaired input a b) (unpairBody_run a b hab)
  · intro V
    simp [diagonalStep, hia, hib]
  · intro V hv
    funext i
    by_cases hi : i = input
    · subst i; simp [unpaired, hv, hia, hib]
    · by_cases ha : i = a
      · subst i; simp [unpaired, hv, hab, Ne.symm hab]
      · by_cases hb : i = b
        · subst i; simp [unpaired, hv]
        · simp [unpaired, hv, hi, ha, hb]
  · intro V v hv
    have hc : pair (advance (V a,V b)).1 (advance (V a,V b)).2 + v =
        pair (V a) (V b) + (v+1) := by rw [advance_pair]; omega
    funext i
    by_cases hi : i = input
    · subst i
      simp [unpaired, diagonalStep, hia, hib]
    · by_cases ha : i = a
      · subst i
        simp [unpaired, diagonalStep, hia, hib, hab,
          Ne.symm hia, Ne.symm hib, Ne.symm hab, hv, hc]
      · by_cases hb : i = b
        · subst i
          simp [unpaired, diagonalStep, hia, hib, hab,
            Ne.symm hia, Ne.symm hib, Ne.symm hab, hv, hc]
        · simp [unpaired, diagonalStep, hi, ha, hb]

/-- One pairing iteration adds the current diagonal's remaining length to
 the output, using the first operand as temporary storage. -/
def pairBody (output a b : Nat) : Code :=
  .seq (.inc output) (.seq (move b [a]) (move a [b,output]))

/-- The pairing body restores its loop counter and zero temporary register,
 adding one plus that counter to the output. -/
theorem pairBody_run (output a b : Nat) (hoa : output ≠ a) (hob : output ≠ b)
    (hab : a ≠ b) (R : Values) (ha : R a = 0) :
    Run (pairBody output a b) R .normal
      (Function.update R output (R output+1+R b)) := by
  let V := Function.update R output (R output+1)
  let W := Function.update (Function.update V b 0) a (V a+V b)
  have h := Run.seq (Run.inc output R)
    (Run.seq (move_one_run b a (Ne.symm hab) V)
      (move_run a [b,output] (by simp [hab, Ne.symm hoa]) W))
  convert h using 1
  · rfl
  · funext i
    by_cases hi : i = output
    · subst i
      simp [transferred, V, W, List.count_cons, ha, hoa, hob, hab,
        Ne.symm hoa, Ne.symm hob, Ne.symm hab]
    · by_cases hia : i = a
      · subst i
        simp [transferred, V, W, ha, hoa, hob, hab, Ne.symm hoa, Ne.symm hab]
      · by_cases hib : i = b
        · subst i
          simp [transferred, V, W, List.count_cons, ha, hoa, hob, hab,
            Ne.symm hoa, Ne.symm hob, Ne.symm hab]
        · simp [transferred, V, W, List.count_cons, hi, hia, hib,
            Ne.symm hi, Ne.symm hia, Ne.symm hib]

/-- Pairing's triangular-number loop consumes the diagonal length. -/
theorem pairLoop_run (output a b : Nat) (hoa : output ≠ a) (hob : output ≠ b)
    (hab : a ≠ b) (R : Values) (ha : R a = 0) :
    Run (.whileDec b (pairBody output a b)) R .normal
      (Function.update (Function.update R b 0) output (R output+tri (R b))) := by
  apply while_invariant b (pairBody output a b) (fun V => V a = 0)
    (fun V => Function.update (Function.update V b 0) output (V output+tri (V b)))
    ?_ ?_ R ha
  · intro V _ hv
    funext i
    by_cases hi : i = output
    · subst i; simp [hv, tri]
    · by_cases hb : i = b
      · subst i; simp [hv, hob, Ne.symm hob]
      · simp [hi, hb]
  · intro V v hva hvb
    let U := Function.update V b v
    let S := Function.update U output (U output+1+U b)
    refine ⟨S, pairBody_run output a b hoa hob hab U (by simp [U, hab, hva]),
      ?_, ?_, ?_⟩
    · simp [S, U, Ne.symm hoa, hab, hva]
    · simp [S, U, Ne.symm hob]
    · funext i
      by_cases hi : i = output
      · subst i; simp [S, U, hob, Ne.symm hob, hvb, tri]; omega
      · by_cases hb : i = b
        · subst i; simp [S, U, Ne.symm hob]
        · simp [S, U, hi, hb]

/-- Destructive Cantor pairing: first accumulate the first operand, then
 consume the combined diagonal length with the triangular-number loop. -/
def pairCode (output a b : Nat) : Code :=
  .seq (move a [b,output]) (.whileDec b (pairBody output a b))

/-- Pairing consumes both operands and adds their Cantor pair to the original
 output. Every other register is preserved. -/
theorem pair_run (output a b : Nat) (hoa : output ≠ a) (hob : output ≠ b)
    (hab : a ≠ b) (R : Values) :
    Run (pairCode output a b) R .normal
      (Function.update (Function.update (Function.update R a 0) b 0)
        output (R output+pair (R a) (R b))) := by
  let V := transferred a [b,output] R
  have h := Run.seq (move_run a [b,output] (by simp [hab, Ne.symm hoa]) R)
    (pairLoop_run output a b hoa hob hab V (by simp [V, transferred]))
  convert h using 1
  · rfl
  · funext i
    by_cases hi : i = output
    · subst i
      simp [V, transferred, List.count_cons, hoa, hob, hab,
        Ne.symm hoa, Ne.symm hob, Ne.symm hab, pair, Nat.add_comm (R b) (R a)]
      omega
    · by_cases hb : i = b
      · subst i; simp [hob, Ne.symm hob]
      · by_cases ha : i = a
        · subst i; simp [V, transferred, hab, Ne.symm hoa]
        · simp [V, transferred, List.count_cons, hi, ha, hb,
            Ne.symm hi, Ne.symm ha, Ne.symm hb]

/-- Subtract the two comparison operands together. If the second runs out
 first, clear the first and leave the enclosing comparison block early. -/
def comparisonLoop (a b : Nat) : Code :=
  .whileDec a (.ifDec b .skip (.seq (clear a) (.breakLoop 1)))

/-- The comparison loop either consumes the first operand and leaves the
 difference in the second, or exits early with both operands zero. -/
theorem comparisonLoop_run (a b : Nat) (hab : a ≠ b) (R : Values) :
    Run (comparisonLoop a b) R (if R a ≤ R b then .normal else .breakLoop 0)
      (Function.update (Function.update R a 0) b (R b-R a)) := by
  have h : ∀ n R, R a = n →
      Run (comparisonLoop a b) R (if n ≤ R b then .normal else .breakLoop 0)
        (Function.update (Function.update R a 0) b (R b-n)) := by
    intro n
    induction n with
    | zero =>
      intro V ha
      have he : Function.update (Function.update V a 0) b (V b-0) = V := by
        funext i
        by_cases hi : i = a
        · subst i; simp [hab, ha]
        · by_cases hb : i = b
          · subst i; simp
          · simp [hi, hb]
      rw [he]
      simpa [comparisonLoop] using (Run.whileZero (body := .ifDec b .skip (.seq (clear a) (.breakLoop 1))) ha)
    | succ n ih =>
      intro V ha
      cases hb : V b with
      | zero =>
        let U := Function.update V a n
        let W := Function.update U a 0
        have body : Run (.ifDec b .skip (.seq (clear a) (.breakLoop 1))) U (.breakLoop 1) W :=
          .ifZero (by simp [U, Ne.symm hab, hb]) (.seq (clear_run a U) (.breakLoop 1 W))
        have hr : Run (comparisonLoop a b) V (.breakLoop 0) W := .whileOuter ha body
        convert hr using 1
        · simp [hb]
        · funext i
          by_cases hi : i = a
          · subst i; simp [W, U, hab]
          · by_cases hi' : i = b
            · subst i; simp [W, U, Ne.symm hab, hb]
            · simp [W, U, hi, hi', hb]
      | succ m =>
        let U := Function.update (Function.update V a n) b m
        have body : Run (.ifDec b .skip (.seq (clear a) (.breakLoop 1)))
            (Function.update V a n) .normal U :=
          .ifPositive (by simp [Ne.symm hab, hb]) (.skip U)
        have tail := ih U (by simp [U, hab])
        have hr := Run.whileNext ha body tail
        convert hr using 1
        · rfl
        · simp [U, hb]
        · funext i
          by_cases hi : i = a
          · subst i; simp [U, hab]
          · by_cases hi' : i = b
            · subst i; simp [U, hb]
            · simp [U, hi, hi']
  exact h (R a) R rfl

/-- The complete equality test clears both operands. It executes its body
 exactly on equality; the surrounding block catches both unequal exits. -/
def ifEqual (a b : Nat) (body : Code) : Code :=
  .block (.seq (comparisonLoop a b)
    (.ifDec b (.seq (clear b) (.breakLoop 0)) body))

/-- Full comparison contract: both operands are consumed in every case, and
 the chosen body runs only when the original values were equal. -/
theorem ifEqual_run (a b : Nat) (hab : a ≠ b) (body : Code) (R S : Values)
    (bodyRun : Run body (Function.update (Function.update R a 0) b 0) .normal S) :
    Run (ifEqual a b body) R .normal
      (if R a = R b then S else Function.update (Function.update R a 0) b 0) := by
  let C := Function.update (Function.update R a 0) b 0
  have loop := comparisonLoop_run a b hab R
  by_cases hle : R a ≤ R b
  · by_cases he : R a = R b
    · have hl : Run (comparisonLoop a b) R .normal C := by
        simpa [hle, he, C] using loop
      have hr : Run (ifEqual a b body) R .normal S :=
        .blockNormal (.seq hl (.ifZero (by simp [C]) bodyRun))
      simpa only [he, ite_true] using hr
    · let v := R b-R a-1
      have hv : R b-R a = v+1 := by dsimp [v]; omega
      let U := Function.update (Function.update R a 0) b (v+1)
      have hl : Run (comparisonLoop a b) R .normal U := by
        simpa only [hle, ite_true, hv] using loop
      have hc : Run (clear b) (Function.update U b v) .normal C := by
        convert clear_run b (Function.update U b v) using 1
        funext i
        by_cases hi : i = b <;> simp [C, U, hi]
      have hr : Run (ifEqual a b body) R .normal C :=
        .blockBreak (.seq hl (.ifPositive (by simp [U]) (.seq hc (.breakLoop 0 C))))
      simpa only [he, ite_false] using hr
  · have he : R a ≠ R b := by omega
    have hz : R b-R a = 0 := by omega
    have hl : Run (comparisonLoop a b) R (.breakLoop 0) C := by
      simpa only [hle, ite_false, hz] using loop
    have hr : Run (ifEqual a b body) R .normal C :=
      .blockBreak (.escape hl (by decide))
    simpa only [he, ite_false] using hr

end TinyZF.Interpreter
