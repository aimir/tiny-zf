import TinyZF.Tape.Registers

/-! # Instruction-pointer arithmetic and dispatch

The 308-state machine recognizes eight consecutive zeros as the left margin.
Within an instruction path, no such run is allowed. The proofs below use the
actual seven dispatch-counter states, and arbitrary finite instruction paths.
-/
namespace TinyZF.Tape.Framework

/-- The instruction DAG's literal entry label, `main().0`. -/
abbrev root : Fin 308 := 65
/-- Dispatch counter after `c` consecutive zeros, with `c ≤ 7`. -/
def cs : Nat → Fin 308
  | 0 => cont 0 | 1 => 49 | 2 => 50 | 3 => 51 | 4 => 52
  | 5 => 53 | 6 => 54 | _ => 55

/-- No eight-zero run occurs while scanning this path from right to left. -/
def nz : Nat → List Bool → Prop
  | _, [] => True
  | _, true :: U => nz 0 U
  | c, false :: U => c < 7 ∧ nz (c+1) U

instance (c : Nat) (U : List Bool) : Decidable (nz c U) := by
  induction U generalizing c with
  | nil => exact isTrue trivial
  | cons b U ih => cases b <;> unfold nz <;> infer_instance

/-- A Boolean version of the zero-run invariant, avoiding construction of
 nested conjunction proofs during each finite certificate evaluation. -/
def checkNz : Nat → List Bool → Bool
  | _, [] => true
  | _, true::U => checkNz 0 U
  | c, false::U => decide (c < 7) && checkNz (c+1) U

/-- Boolean zero-run checking is exactly the original tape invariant. -/
theorem checkNz_iff (c : Nat) (U : List Bool) : checkNz c U = true ↔ nz c U := by
  induction U generalizing c with
  | nil => simp [checkNz, nz]
  | cons b U ih => cases b <;> simp [checkNz, nz, ih]

/-- Starting with one fewer counted zero preserves a valid path. -/
theorem nz_mono (c : Nat) (U : List Bool) (h : nz (c+1) U) : nz c U := by
  induction U generalizing c with
  | nil => trivial
  | cons b U ih =>
    cases b
    · exact ⟨by have := h.1; omega, ih (c+1) h.2⟩
    · exact h

/-- A suffix of a valid instruction path remains valid. -/
theorem nz_tail (b : Bool) (U : List Bool) (h : nz 0 (b :: U)) : nz 0 U := by
  cases b
  · exact nz_mono 0 U h.2
  · exact h

/-- Selector marks contain no zero and therefore preserve path validity. -/
theorem nz_ones (k : Nat) (U : List Bool) : nz 0 (ones k ++ U) ↔ nz 0 U := by
  induction k with
  | zero => rfl
  | succ k ih => exact ih

/-- A one resets the dispatch counter. -/
theorem cs_one (c : Nat) (hc : c ≤ 7) :
    m (cs c) true = some ⟨true, false, some (cont 0)⟩ := by
  interval_cases c <;> rfl
/-- Before the eighth zero, a zero increments the dispatch counter. -/
theorem cs_zero (c : Nat) (hc : c < 7) :
    m (cs c) false = some ⟨false, false, some (cs (c+1))⟩ := by
  interval_cases c <;> rfl

/-- At the infinite blank left margin, dispatch turns around and returns to
 the instruction DAG immediately to the right of its marker. -/
theorem disp0 (Y : List Bool) :
    Progress m (zl (cont 0) [] (true :: Y)) (zc root [true] Y) := by
  rw [zl_nil]
  zrun
  convert Exec.refl m _ using 1 <;> simp [zc, pref, blanks, cons_blanks]

/-- Dispatch preserves the entire path and following data, provided it cannot
 mistake an internal run of zeros for the blank left margin. -/
theorem disp_gen (U : List Bool) (c : Nat) (Y : List Bool) (hc : c ≤ 7) (h : nz c U) :
    Progress m (zl (cs c) (U ++ [true]) Y) (zc root [true] (U.reverse ++ Y)) := by
  induction U generalizing c Y with
  | nil =>
    simp only [List.append_eq, List.nil_append, List.reverse_nil, zl_cons]
    apply Progress.prepend (moveL _ _ _ _ _ _ (cs_one c hc))
    exact (disp0 Y).exec
  | cons b U ih =>
    simp only [List.append_eq, List.cons_append, zl_cons]
    cases b
    · apply Progress.prepend (moveL _ _ _ _ _ _ (cs_zero c h.1))
      convert (ih (c+1) (false :: Y) (by have := h.1; omega) h.2).exec using 1 <;> first | rfl |
        simp only [List.append_eq, List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append]
    · apply Progress.prepend (moveL _ _ _ _ _ _ (cs_one c hc))
      convert (ih 0 (true :: Y) (by omega) h).exec using 1 <;> first | rfl |
        simp only [List.append_eq, List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append]

/-- Ordinary dispatch starts with an empty zero count. -/
theorem disp (U Y : List Bool) (h : nz 0 U) :
    Progress m (zl (cont 0) (U ++ [true]) Y) (zc root [true] (U.reverse ++ Y)) :=
  disp_gen U 0 Y (by omega) h

/-- Binary increment, on a path written least-significant bit first. A carry
 escaping the old path is represented by a moved tape marker. -/
def incRev : List Bool → List Bool
  | [] => []
  | false :: U => true :: U
  | true :: U => false :: incRev U

/-- Remove the suffix through the `k`-th selected kind of ancestor edge. -/
def stripRev (b : Bool) : Nat → List Bool → List Bool
  | 0, U => U
  | _+1, [] => []
  | k+1, a :: U => if a = b then stripRev b k U else stripRev b (k+1) U

/-- A zero-level strip leaves every path intact. -/
@[simp] theorem stripRev_zero (b : Bool) (U : List Bool) : stripRev b 0 U = U := by cases U <;> rfl
/-- Binary increment preserves the represented path's length. -/
@[simp] theorem incRev_length (U : List Bool) : (incRev U).length = U.length := by
  induction U with
  | nil => rfl
  | cons b U ih => cases b <;> simp [incRev, ih]

/-- Break-state indices are bounded by the literal machine's three routines. -/
def breakState (k : Nat) : Fin 308 := brk ⟨min k 2, by omega⟩
/-- Continue-state indices are bounded by its five routines. -/
def continueState (k : Nat) : Fin 308 := cont ⟨min k 4, by omega⟩

/-- A break discards ones while looking for a zero ancestor. -/
theorem break_one (k : Nat) :
    m (breakState k) true = some ⟨false, false, some (breakState k)⟩ := by
  have h : ∀ j : Fin 3, m (brk j) true = some ⟨false, false, some (brk j)⟩ := by decide
  exact h ⟨min k 2, by omega⟩
/-- Finding a zero discharges one pending break level. -/
theorem break_succ (k : Nat) (hk : k ≤ 1) :
    m (breakState (k+1)) false = some ⟨false, false, some (breakState k)⟩ := by
  interval_cases k <;> rfl
/-- Finding a one discharges one pending continue level. -/
theorem continue_succ_one (k : Nat) (hk : k ≤ 3) :
    m (continueState (k+1)) true = some ⟨false, false, some (continueState k)⟩ := by
  interval_cases k <;> rfl
/-- A continue discards zeros while looking for a one ancestor. -/
theorem continue_succ_zero (k : Nat) (hk : k ≤ 3) :
    m (continueState (k+1)) false = some ⟨false, false, some (continueState (k+1))⟩ := by
  interval_cases k <;> rfl

-- Finish symbolic traces when the two finite views differ only by blank padding.
macro "crun" : tactic => `(tactic|
  repeat first
  | exact Exec.refl _ _
  | (solve | (refine ⟨0, ?_⟩; simp [iterate, zc, pref]))
  | zstep
  | (rw [zl_cons])
  | (rw [zl_nil]))

/-- Breaking `k` levels strips `k` zero ancestors and increments the remaining
 binary path. Erased suffix cells become gap zeros; no space is lost. -/
theorem break_ip (U : List Bool) (k : Nat) (Y : List Bool) (hk : k ≤ 2) (h : nz 0 U) :
    ∃ g, Progress m (zl (breakState k) (U ++ [true]) Y)
      (zc root [true] ((incRev (stripRev false k U)).reverse ++ zeros g ++ Y)) ∧
      U.length ≤ (stripRev false k U).length + g := by
  induction U generalizing k Y with
  | nil =>
    refine ⟨k+1, ?_, by simp [stripRev]⟩
    interval_cases k <;>
      simp only [List.append_eq, List.nil_append, stripRev, incRev, List.reverse_nil, List.replicate_succ,
        List.replicate_zero, List.cons_append, zl_cons] <;> crun
  | cons b U ih =>
    have ht := nz_tail b U h
    cases b with
    | false =>
      cases k with
      | zero =>
        refine ⟨0, ?_, by simp [stripRev]⟩
        simp only [List.append_eq, List.cons_append, zl_cons]
        apply Progress.prepend (moveL _ _ _ _ _ _ (by rfl))
        convert (disp U (true :: Y) ht).exec using 1 <;> first | rfl |
          simp only [List.append_eq, stripRev_zero, incRev, List.reverse_cons, List.append_assoc,
            List.cons_append, List.nil_append, List.replicate_zero, List.append_nil]
      | succ k =>
        obtain ⟨g, hg, hlen⟩ := ih k (false :: Y) (by omega) ht
        refine ⟨g+1, ?_, ?_⟩
        · simp only [List.append_eq, List.cons_append, zl_cons]
          apply Progress.prepend (moveL _ _ _ _ _ _ (break_succ k (by omega)))
          convert hg.exec using 1 <;> first | rfl |
            simp only [List.append_eq, stripRev, ↓reduceIte, List.append_assoc, List.replicate_succ,
              List.cons_append, replicate_comm]
        · simp only [stripRev, ↓reduceIte, List.length_cons]; omega
    | true =>
      cases k with
      | zero =>
        obtain ⟨g, hg, hlen⟩ := ih 0 (false :: Y) (by omega) ht
        refine ⟨g, ?_, ?_⟩
        · simp only [List.append_eq, List.cons_append, zl_cons]
          apply Progress.prepend (moveL _ _ _ _ _ _ (break_one 0))
          convert hg.exec using 1 <;> first | rfl |
            simp only [List.append_eq, stripRev_zero, incRev, List.reverse_cons, List.append_assoc,
              List.cons_append, List.nil_append, replicate_comm]
        · simp only [List.append_eq, stripRev_zero, List.length_cons]; omega
      | succ k =>
        obtain ⟨g, hg, hlen⟩ := ih (k+1) (false :: Y) hk ht
        refine ⟨g+1, ?_, ?_⟩
        · simp only [List.append_eq, List.cons_append, zl_cons]
          apply Progress.prepend (moveL _ _ _ _ _ _ (break_one (k+1)))
          convert hg.exec using 1 <;> first | rfl |
            simp only [List.append_eq, stripRev, Bool.true_eq_false, ↓reduceIte, List.append_assoc,
              List.replicate_succ, List.cons_append, replicate_comm]
        · simp only [List.append_eq, stripRev, Bool.true_eq_false, ↓reduceIte, List.length_cons]; omega

/-- Continuing `k` levels strips through `k` one ancestors and dispatches to
 the corresponding loop head. The count condition keeps the initial marker. -/
theorem continue_ip (U : List Bool) (k : Nat) (Y : List Bool) (hk : k ≤ 4)
    (h : nz 0 U) (hc : k ≤ U.count true) :
    ∃ g, Progress m (zl (continueState k) (U ++ [true]) Y)
      (zc root [true] ((stripRev true k U).reverse ++ zeros g ++ Y)) ∧
      U.length ≤ (stripRev true k U).length + g := by
  induction U generalizing k Y with
  | nil =>
    have : k = 0 := by simp at hc; omega
    subst k
    refine ⟨0, ?_, by simp [stripRev]⟩
    simpa [continueState, cont, stripRev] using disp [] Y h
  | cons b U ih =>
    have ht := nz_tail b U h
    cases k with
    | zero =>
      refine ⟨0, ?_, by simp⟩
      simpa [continueState, cont] using disp (b :: U) Y h
    | succ k =>
      cases b
      · have hc' : k+1 ≤ U.count true := by simpa using hc
        obtain ⟨g, hg, hlen⟩ := ih (k+1) (false :: Y) hk ht hc'
        refine ⟨g+1, ?_, ?_⟩
        · simp only [List.append_eq, List.cons_append, zl_cons]
          apply Progress.prepend (moveL _ _ _ _ _ _ (continue_succ_zero k (by omega)))
          convert hg.exec using 1 <;> first | rfl |
            simp only [List.append_eq, stripRev, Bool.false_eq_true, ↓reduceIte, List.append_assoc,
              List.replicate_succ, List.cons_append, replicate_comm]
        · simp only [List.append_eq, stripRev, Bool.false_eq_true, ↓reduceIte, List.length_cons]; omega
      · have hc' : k ≤ U.count true := by simpa using hc
        obtain ⟨g, hg, hlen⟩ := ih k (false :: Y) (by omega) ht hc'
        refine ⟨g+1, ?_, ?_⟩
        · simp only [List.append_eq, List.cons_append, zl_cons]
          apply Progress.prepend (moveL _ _ _ _ _ _ (continue_succ_one k (by omega)))
          convert hg.exec using 1 <;> first | rfl |
            simp only [List.append_eq, stripRev, ↓reduceIte, List.append_assoc,
              List.replicate_succ, List.cons_append, replicate_comm]
        · simp only [List.append_eq, stripRev, ↓reduceIte, List.length_cons]; omega

end TinyZF.Tape.Framework
