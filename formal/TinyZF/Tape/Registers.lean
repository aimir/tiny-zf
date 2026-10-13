import TinyZF.Tape.Core
import TinyZF.Machine308

/-! # Unary register operations on the literal tape

A value `v` is stored as `v+1` ones. Single zeros separate registers;
a double zero selects the register on its right. These contracts quantify
arbitrary register values and arbitrary surrounding tape. State numbers
are indices into the literal `Machine308.table`.
-/
namespace TinyZF.Tape

abbrev ones (n : Nat) := List.replicate n true
abbrev zeros (n : Nat) := List.replicate n false

/-- Registers in rightward order, each preceded by its separator. -/
def sepsR (vs : List Nat) : List Bool := vs.flatMap (fun v => false :: ones (v+1))
/-- Registers viewed leftwards, each followed by its separator. -/
def sepsL (vs : List Nat) : List Bool := vs.flatMap (fun v => ones (v+1) ++ [false])

/-- Decompose the first right-facing register. -/
@[simp] theorem sepsR_cons (v : Nat) (vs : List Nat) :
    sepsR (v :: vs) = false :: true :: ones v ++ sepsR vs := rfl
/-- Decompose the first left-facing register. -/
@[simp] theorem sepsL_cons (v : Nat) (vs : List Nat) :
    sepsL (v :: vs) = true :: ones v ++ false :: sepsL vs := by
  simp [sepsL, List.replicate_succ, List.append_assoc]
/-- Empty register files contain no cells. -/
@[simp] theorem sepsR_nil : sepsR [] = [] := rfl
/-- Empty left-facing register files contain no cells. -/
@[simp] theorem sepsL_nil : sepsL [] = [] := rfl
/-- Register encodings respect concatenation. -/
@[simp] theorem sepsR_append (a b : List Nat) : sepsR (a ++ b) = sepsR a ++ sepsR b := by simp [sepsR]
/-- The left-facing encoding also respects concatenation. -/
@[simp] theorem sepsL_append (a b : List Nat) : sepsL (a ++ b) = sepsL a ++ sepsL b := by simp [sepsL]
/-- Reversing the tape exchanges the two separator conventions. -/
@[simp] theorem reverse_sepsR (vs : List Nat) : (sepsR vs).reverse = sepsL vs.reverse := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    simp only [List.append_eq, sepsR_cons, List.reverse_cons, List.reverse_append, List.reverse_replicate,
      ih, sepsL_append, sepsL_cons, sepsL_nil]
    simp [List.append_assoc, ← List.replicate_succ, List.replicate_succ']
/-- Reversing the left-facing encoding recovers the right-facing encoding. -/
@[simp] theorem reverse_sepsL (vs : List Nat) : (sepsL vs).reverse = sepsR vs.reverse := by
  rw [← List.reverse_reverse vs, ← reverse_sepsR, List.reverse_reverse, List.reverse_reverse]
/-- Appending a register prepends its reversed representation. -/
theorem sepsL_reverse_cons (v : Nat) (vs : List Nat) :
    sepsL (v :: vs).reverse = sepsL vs.reverse ++ ones (v+1) ++ [false] := by
  simp [sepsL, List.flatMap_append, List.append_assoc]
/-- A final separator changes right-facing to left-facing conventions. -/
theorem sepsR_snoc (vs : List Nat) : sepsR vs ++ [false] = false :: sepsL vs := by
  induction vs with
  | nil => rfl
  | cons v vs ih => simpa only [sepsR_cons, sepsL_cons, List.cons_append, List.append_assoc] using congrArg (fun l => false :: true :: ones v ++ l) ih

namespace Framework
abbrev m := Machine308.machine
abbrev qDec : Fin 308 := 5
abbrev qDecB : Fin 308 := 6
abbrev qDecC : Fin 308 := 7
abbrev qDecD : Fin 308 := 8
abbrev qDecE : Fin 308 := 9
abbrev qDecG : Fin 308 := 10
abbrev qDecH : Fin 308 := 11
abbrev qDecI : Fin 308 := 12
abbrev qInc : Fin 308 := 13
abbrev qIncB : Fin 308 := 14
abbrev qIncC : Fin 308 := 15
abbrev qIncD : Fin 308 := 16
abbrev qSel : Fin 308 := 17
abbrev qSelB : Fin 308 := 18
abbrev qSelC : Fin 308 := 19
abbrev qSelD : Fin 308 := 20
abbrev qSelE : Fin 308 := 21
abbrev qSelF : Fin 308 := 22
abbrev qRet1 : Fin 308 := 23
abbrev qRet1A : Fin 308 := 24
abbrev qRet1B : Fin 308 := 25
abbrev qRet2 : Fin 308 := 26
abbrev qRet2A : Fin 308 := 27
abbrev qRet2B : Fin 308 := 28
abbrev brk (k : Fin 3) : Fin 308 := ⟨57 + k.val, by omega⟩
abbrev cont (k : Fin 5) : Fin 308 := ⟨60 + k.val, by omega⟩

-- Each symbolic step checks its table entry by kernel reduction.
macro "zstep" : tactic => `(tactic|
  first
  | (apply Progress.prepend; · apply moveR; rfl)
  | (apply Progress.prepend; · apply moveL; rfl)
  | (apply Exec.prepend; · apply moveR; rfl)
  | (apply Exec.prepend; · apply moveL; rfl))
macro "lnorm" : tactic => `(tactic| simp only [List.append_eq, List.append_assoc, List.cons_append, List.nil_append])
macro "zrun" : tactic => `(tactic|
  repeat first | exact Exec.refl _ _ | zstep | (rw [zl_cons]) | (rw [zl_nil]))

/-- The selector's forward scan crosses the preceding registers and stops at
 the double separator, leaving all encoded values unchanged. -/
theorem selC (B : List Nat) (l X : List Bool) :
    Progress m (zc qSelC l (sepsR B ++ false :: false :: X))
      (zc qSelE (sepsL B.reverse ++ l) (false :: false :: X)) := by
  induction B generalizing l with
  | nil => simp only [List.append_eq, sepsR_nil, List.reverse_nil, sepsL_nil, List.nil_append]; zrun
  | cons b B ih =>
    rw [sepsR_cons]; lnorm
    zstep; zstep
    apply Exec.trans (scanR qSelC true b _ _ (by rfl))
    rw [sepsL_reverse_cons]
    convert (ih (ones b ++ true :: false :: l)).exec using 1 <;>
      simp only [List.append_eq, List.append_assoc, List.cons_append, List.nil_append,
        List.replicate_succ, replicate_comm]

/-- Enter the selector scan through its first-register state. -/
theorem selB (b : Nat) (B : List Nat) (l X : List Bool) :
    Progress m (zc qSelB l (sepsR (b :: B) ++ false :: false :: X))
      (zc qSelE (sepsL (b :: B).reverse ++ l) (false :: false :: X)) := by
  rw [sepsR_cons]; lnorm
  zstep; zstep
  apply Exec.trans (scanR qSelC true b _ _ (by rfl))
  rw [sepsL_reverse_cons]
  convert (selC B (ones b ++ true :: false :: l) X).exec using 1 <;>
    simp only [List.append_eq, List.append_assoc, List.cons_append, List.nil_append,
      List.replicate_succ, replicate_comm]

/-- The increment scan crosses the prefix then replaces the second selection
 zero by one, increasing the selected unary value. -/
theorem incC (B : List Nat) (l X : List Bool) :
    Progress m (zc qIncC l (sepsR B ++ false :: false :: X))
      (zc qRet1 (sepsL B.reverse ++ l) (false :: true :: X)) := by
  induction B generalizing l with
  | nil => simp only [List.append_eq, sepsR_nil, List.reverse_nil, sepsL_nil, List.nil_append]; zrun
  | cons b B ih =>
    rw [sepsR_cons]; lnorm
    zstep; zstep
    apply Exec.trans (scanR qIncC true b _ _ (by rfl))
    rw [sepsL_reverse_cons]
    convert (ih (ones b ++ true :: false :: l)).exec using 1 <;>
      simp only [List.append_eq, List.append_assoc, List.cons_append, List.nil_append,
        List.replicate_succ, replicate_comm]

/-- Enter the increment scan through its first-register state. -/
theorem incB (b : Nat) (B : List Nat) (l X : List Bool) :
    Progress m (zc qIncB l (sepsR (b :: B) ++ false :: false :: X))
      (zc qRet1 (sepsL (b :: B).reverse ++ l) (false :: true :: X)) := by
  rw [sepsR_cons]; lnorm
  zstep; zstep
  apply Exec.trans (scanR qIncC true b _ _ (by rfl))
  rw [sepsL_reverse_cons]
  convert (incC B (ones b ++ true :: false :: l) X).exec using 1 <;>
    simp only [List.append_eq, List.append_assoc, List.cons_append, List.nil_append,
      List.replicate_succ, replicate_comm]

/-- The return scan crosses every earlier register and the blank gap, erases
 the temporary marker, and hands control to the designated IP routine. -/
theorem ret_gen (r ra rb t : Fin 308)
    (h0 : m r false = some ⟨false, false, some ra⟩)
    (h1 : m r true = some ⟨true, false, some r⟩)
    (ha0 : m ra false = some ⟨false, false, some rb⟩)
    (ha1 : m ra true = some ⟨true, false, some r⟩)
    (hb0 : m rb false = some ⟨false, false, some rb⟩)
    (hb1 : m rb true = some ⟨false, false, some t⟩)
    (B : List Nat) (k : Nat) (L Y : List Bool) :
    Progress m (zc r (sepsL B ++ zeros (k+1) ++ true :: L) (false :: Y))
      (zl t L (false :: zeros (k+1) ++ (sepsL B).reverse ++ false :: Y)) := by
  induction B generalizing Y with
  | nil =>
    simp only [List.append_eq, sepsL_nil, List.reverse_nil, List.nil_append, List.replicate_succ]
    lnorm
    apply Progress.prepend (moveL _ _ _ _ _ _ h0)
    rw [zl_cons]
    apply Exec.prepend (moveL _ _ _ _ _ _ ha0)
    apply Exec.trans (scanL rb false k _ _ hb0)
    rw [zl_cons]
    apply Exec.prepend (moveL _ _ _ _ _ _ hb1)
    convert Exec.refl m _ using 1 <;> simp only [List.append_eq, replicate_comm, List.cons_append]
  | cons v B ih =>
    rw [sepsL_cons]
    simp only [List.append_eq, List.reverse_cons, List.reverse_append, List.reverse_replicate]
    lnorm
    apply Progress.prepend (moveL _ _ _ _ _ _ h0)
    rw [zl_cons]
    apply Exec.prepend (moveL _ _ _ _ _ _ ha1)
    apply Exec.trans (scanL r true v _ _ h1)
    rw [zl_cons]
    convert (ih (ones v ++ true :: false :: Y)).exec using 1 <;>
      simp only [List.append_eq, List.append_assoc, List.cons_append, List.nil_append]

/-- The ordinary return enters the increment-and-dispatch IP routine. -/
theorem ret1 (B : List Nat) (k : Nat) (L Y : List Bool) :
    Progress m (zc qRet1 (sepsL B ++ zeros (k+1) ++ true :: L) (false :: Y))
      (zl (brk 0) L (false :: zeros (k+1) ++ (sepsL B).reverse ++ false :: Y)) :=
  ret_gen qRet1 qRet1A qRet1B (brk 0) rfl rfl rfl rfl rfl rfl B k L Y

/-- The zero-decrement return skips one extra instruction block. -/
theorem ret2 (B : List Nat) (k : Nat) (L Y : List Bool) :
    Progress m (zc qRet2 (sepsL B ++ zeros (k+1) ++ true :: L) (false :: Y))
      (zl (brk 1) L (false :: zeros (k+1) ++ (sepsL B).reverse ++ false :: Y)) :=
  ret_gen qRet2 qRet2A qRet2B (brk 1) rfl rfl rfl rfl rfl rfl B k L Y

/-- The decrement forward pass shifts each register before the selected one
 right by a cell, providing space for instruction-pointer growth. -/
theorem decC (n : Nat) (B : List Nat) (l X : List Bool) :
    Progress m (zc qDecC l (ones n ++ sepsR B ++ false :: false :: X))
      (zc qDecE (false :: sepsL B.reverse ++ ones (n+1) ++ l) X) := by
  lnorm
  induction B generalizing n l with
  | nil =>
    apply Exec.trans_progress (scanR qDecC true n _ _ (by rfl))
    simp only [List.append_eq, sepsR_nil, sepsL_nil, List.reverse_nil, List.nil_append]
    zstep; zstep
    convert Exec.refl m _ using 1 <;> simp only [List.append_eq, List.replicate_succ, replicate_comm, List.cons_append]
  | cons b B ih =>
    apply Exec.trans_progress (scanR qDecC true n _ _ (by rfl))
    rw [sepsR_cons]; lnorm
    zstep; zstep
    rw [sepsL_reverse_cons]
    convert (ih b (false :: true :: ones n ++ l)).exec using 1 <;>
      simp only [List.append_eq, List.append_assoc, List.cons_append, List.nil_append, List.replicate_succ, replicate_comm]

/-- The selected positive unary block loses one mark and gains the moving
 double separator used to shift the rest of the register file. -/
theorem decE (u v k : Nat) (L R : List Bool) (h : u+v=k+2) :
    Progress m (zc qDecE (ones u ++ L) (ones v ++ false :: R))
      (zc qDecI (true :: false :: ones (k+1) ++ L) R) := by
  apply Exec.trans_progress (scanR qDecE true v _ _ (by rfl))
  rw [← List.append_assoc, ← List.replicate_add, Nat.add_comm v u, h]
  simp only [List.append_eq, List.replicate_succ, List.cons_append]
  zrun

/-- The decrement's shift loop traverses every register to the right of the
 selected one, preserving those values, and then starts the return scan. -/
theorem decLoop (C : List Nat) (L Z : List Bool) :
    Progress m (zc qDecI (true :: false :: L) (sepsL C ++ false :: Z))
      (zl qRet1 (false :: sepsL C.reverse ++ L) (false :: false :: Z)) := by
  induction C generalizing L with
  | nil => simp only [List.append_eq, sepsL_nil, List.reverse_nil, List.nil_append]; zrun
  | cons c C ih =>
    rw [sepsL_cons]; lnorm
    zstep
    apply Exec.trans (decE 2 c c (false :: L) _ (by omega)).exec
    rw [sepsL_reverse_cons]
    convert (ih (ones (c+1) ++ false :: L)).exec using 1 <;>
      simp only [List.append_eq, List.append_assoc, List.cons_append, List.nil_append]

/-- Enter the decrement's first-register scan for a nonempty prefix. -/
theorem decB (A : List Nat) (l X : List Bool) (hA : A ≠ []) :
    Progress m (zc qDecB l (sepsR A ++ false :: false :: X))
      (zc qDecE (false :: sepsL A.reverse ++ false :: l) X) := by
  cases A with
  | nil => contradiction
  | cons a A =>
    rw [sepsR_cons]; lnorm
    zstep; zstep
    rw [sepsL_reverse_cons]
    convert (decC a A (false :: false :: l) X).exec using 1 <;>
      simp only [List.append_eq, List.append_assoc, List.cons_append, List.nil_append]

/-- Decrement entry writes the temporary return marker, scans the gap, and
 reaches the selected register after shifting its nonempty prefix. -/
theorem decStart (L : List Bool) (z : Nat) (A : List Nat) (X : List Bool) (hA : A ≠ []) :
    Progress m (zc qDec L (false :: zeros z ++ sepsR A ++ false :: false :: X))
      (zc qDecE (false :: sepsL A.reverse ++ zeros (z+1) ++ true :: L) X) := by
  lnorm
  zstep
  apply Exec.trans (scanR qDecB false z _ _ (by rfl))
  convert (decB A (zeros z ++ true :: L) X hA).exec using 1 <;>
    simp only [List.append_eq, List.append_assoc, List.cons_append, List.nil_append, List.replicate_succ]

/-- The selector moves left across precisely one register. The value is
 unchanged, and the double separator moves to its left. -/
theorem sel_op (L : List Bool) (z : Nat) (A : List Nat) (v : Nat) (X : List Bool)
    (hz : 1 ≤ z) :
    Progress m (zc qSel L (false :: zeros z ++ sepsR (A ++ [v]) ++ false :: false :: X))
      (zl (brk 0) L (false :: zeros z ++ sepsR A ++ false :: false :: ones (v+1) ++ false :: X)) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : z ≠ 0)
  obtain ⟨b, B, hB⟩ : ∃ b B, A ++ [v] = b :: B := by
    cases A with
    | nil => exact ⟨v, [], rfl⟩
    | cons a A => exact ⟨a, A ++ [v], rfl⟩
  lnorm
  zstep
  apply Exec.trans (scanR qSelB false (k+1) _ _ (by rfl))
  rw [hB]
  apply Exec.trans (selB b B _ _).exec
  rw [← hB, List.reverse_append]
  simp only [List.append_eq, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, sepsL_cons]
  lnorm
  zstep
  apply Exec.trans (scanL qSelF true (v+1) _ _ (by rfl))
  rw [zl_cons]
  zstep; zstep
  rw [zl_cons]
  apply Exec.trans (by simpa only [List.append_assoc, List.cons_append] using (ret1 A.reverse k L _).exec)
  convert Exec.refl m _ using 1 <;>
    simp only [List.append_eq, reverse_sepsL, List.reverse_reverse, List.append_assoc,
      List.cons_append, List.replicate_succ, replicate_comm]

/-- Increment the selected register and remove its double separator. A
 nonempty earlier prefix and a positive gap protect the instruction pointer. -/
theorem inc_op (L : List Bool) (z : Nat) (A : List Nat) (v : Nat) (Y : List Bool)
    (hz : 1 ≤ z) (hA : A ≠ []) :
    Progress m (zc qInc L (false :: zeros z ++ sepsR A ++ false :: false :: ones (v+1) ++ Y))
      (zl (brk 0) L (false :: zeros z ++ sepsR A ++ false :: ones (v+2) ++ Y)) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : z ≠ 0)
  cases A with
  | nil => contradiction
  | cons a A =>
    lnorm
    zstep
    apply Exec.trans (scanR qIncB false (k+1) _ _ (by rfl))
    apply Exec.trans (incB a A _ _).exec
    apply Exec.trans (by simpa only [List.append_assoc, List.cons_append] using (ret1 (a :: A).reverse k L _).exec)
    convert Exec.refl m _ using 1 <;>
      simp only [List.append_eq, reverse_sepsL, List.reverse_reverse, List.append_assoc,
        List.cons_append, List.replicate_succ]

/-- A positive decrement removes one unary mark and shifts the entire file
 right by one cell. The instruction-pointer gap therefore grows by one. -/
theorem dec_pos_op (L : List Bool) (z : Nat) (A : List Nat) (v : Nat) (C : List Nat)
    (hA : A ≠ []) :
    Progress m (zc qDec L (false :: zeros z ++ sepsR A ++ false :: false :: ones (v+2) ++ sepsR C))
      (zl (brk 0) L (false :: zeros (z+1) ++ sepsR (A ++ v :: C))) := by
  rw [← zc_padr qDec L _ 2, ← zl_padr (brk 0) L _ 3]
  lnorm
  have hC : sepsR C ++ zeros 2 = false :: sepsL C ++ [false] := by
    change sepsR C ++ ([false] ++ [false]) = _
    rw [← List.append_assoc, sepsR_snoc]
  rw [hC]; lnorm
  apply Progress.trans (by simpa only [List.append_assoc, List.cons_append] using decStart L z A _ hA)
  apply Progress.trans (decE 0 (v+2) v _ _ (by omega))
  apply Progress.trans (decLoop C _ _)
  lnorm
  rw [zl_cons]
  have hF : sepsL C.reverse ++ ones (v+1) ++ false :: sepsL A.reverse ++ zeros (z+1) ++ true :: L =
      sepsL (A ++ v :: C).reverse ++ zeros (z+1) ++ true :: L := by
    simp [List.reverse_append, List.reverse_cons, sepsL_append, sepsL_cons,
      List.append_assoc, List.replicate_succ]
  simp only [List.append_eq, List.append_assoc, List.cons_append, List.nil_append] at hF ⊢
  rw [hF]
  apply Progress.trans_exec (by simpa only [List.append_assoc, List.cons_append] using ret1 (A ++ v :: C).reverse z L _)
  convert Exec.refl m _ using 1 <;>
    simp only [List.append_eq, reverse_sepsL, List.reverse_reverse, List.append_assoc,
      List.cons_append, List.nil_append, List.replicate_succ, List.replicate_zero]

/-- Decrementing a zero register preserves its zero value, shifts the file,
 and returns through `break.1`, implementing the register machine's zero branch. -/
theorem dec_zero_op (L : List Bool) (z : Nat) (A C : List Nat) (hA : A ≠ []) :
    Progress m (zc qDec L (false :: zeros z ++ sepsR A ++ false :: false :: true :: sepsR C))
      (zl (brk 1) L (false :: zeros (z+1) ++ sepsR (A ++ 0 :: C))) := by
  rw [← zc_padr qDec L _ 1, ← zl_padr (brk 1) L _ 1]
  rw [sepsR_append, sepsR_cons]
  lnorm
  rw [show sepsR C ++ zeros 1 = false :: sepsL C from sepsR_snoc C]
  apply Progress.trans (by simpa only [List.append_assoc, List.cons_append] using decStart L z A _ hA)
  zstep; zstep
  rw [zl_cons]
  zstep
  rw [zl_cons]
  zstep
  have hne : A.reverse ≠ [] := by simpa using hA
  cases hrev : A.reverse with
  | nil => exact False.elim (hne hrev)
  | cons a B =>
    rw [sepsL_cons]
    lnorm
    apply Exec.trans (scanL qRet2 true (a+1) _ _ (by rfl))
    rw [zl_cons]
    apply Exec.trans (by simpa only [List.append_assoc, List.cons_append] using (ret2 B z L _).exec)
    have hAr : sepsR A = (sepsL (a :: B)).reverse := by rw [← hrev, reverse_sepsL, List.reverse_reverse]
    rw [hAr]
    convert Exec.refl m _ using 1 <;>
      simp only [List.append_eq, sepsL_cons, List.reverse_cons, List.reverse_append, List.reverse_replicate,
        List.append_assoc, List.cons_append, List.nil_append, List.replicate_succ,
        List.replicate_zero, replicate_comm]

/-- The register-address chains use the candidate's ten physical registers,
 starting with prooflist at index zero. -/
def regState (dec : Bool) (r : Nat) : Fin 308 :=
  let inc : Fin 308 := match r with
    | 0 => 40 | 1 => 32 | 2 => 46 | 3 => 48 | 4 => 30
    | 5 => 34 | 6 => 36 | 7 => 38 | 8 => 42 | _ => 44
  if dec then ⟨inc.val - 1, by omega⟩ else inc

/-- A zero in an address chain starts another selector pass. -/
theorem reg_zero (dec : Bool) (r : Nat) (hr : r ≤ 9) :
    m (regState dec r) false = some ⟨false, true, some qSel⟩ := by
  interval_cases r <;> cases dec <;> rfl
/-- A one advances one link along the physical register-address chain. -/
theorem reg_succ (dec : Bool) (r : Nat) (hr : r ≤ 8) :
    m (regState dec (r+1)) true = some ⟨true, true, some (regState dec r)⟩ := by
  interval_cases r <;> cases dec <;> rfl
/-- The final address-chain one enters the requested primitive operation. -/
theorem reg_last (dec : Bool) :
    m (regState dec 0) true = some ⟨true, true, some (if dec then qDec else qInc)⟩ := by
  cases dec <;> rfl

/-- An incomplete address chain adds a selector mark; repeated dispatch passes
 therefore reach exactly the requested register. -/
theorem chain_sel (dec : Bool) (r j : Nat) (l X : List Bool) (hr : r ≤ 9) (hj : j ≤ r) :
    Progress m (zc (regState dec r) l (ones j ++ false :: X))
      (zc qSel (false :: ones j ++ l) X) := by
  induction j generalizing r l with
  | zero =>
    apply Progress.prepend (moveR _ _ _ _ _ _ (reg_zero dec r hr))
    exact Exec.refl _ _
  | succ j ih =>
    cases r with
    | zero => omega
    | succ r =>
      apply Progress.prepend (moveR _ _ _ _ _ _ (reg_succ dec r (by omega)))
      convert (ih r (true :: l) (by omega) (by omega)).exec using 1 <;>
        simp only [List.append_eq, List.replicate_succ, List.cons_append, replicate_comm]

/-- A completed address chain enters increment or decrement after precisely
 `r+1` unary selector marks. -/
theorem chain_op (dec : Bool) (r : Nat) (l X : List Bool) (hr : r ≤ 9) :
    Progress m (zc (regState dec r) l (ones (r+1) ++ X))
      (zc (if dec then qDec else qInc) (ones (r+1) ++ l) X) := by
  induction r generalizing l with
  | zero =>
    apply Progress.prepend (moveR _ _ _ _ _ _ (reg_last dec))
    exact Exec.refl _ _
  | succ r ih =>
    apply Progress.prepend (moveR _ _ _ _ _ _ (reg_succ dec r (by omega)))
    convert (ih (true :: l) (by omega)).exec using 1 <;>
      simp only [List.append_eq, List.replicate_succ, List.cons_append, replicate_comm]

end Framework
end TinyZF.Tape
