import TinyZF.Tape.Paths

/-! # Complete register-instruction cycles

The physical file stores ten registers in reverse address order, after the
unused bootstrap prefix. Selector passes move a double separator to the
requested register; one final pass performs the operation and returns to the
instruction root. These lemmas compose the literal transition contracts and
track how much blank space remains available for the instruction pointer.
-/
namespace TinyZF.Tape.Framework

/-- Arithmetic register values indexed by their physical address. Only
 addresses below ten are accessed by the certified instruction paths. -/
abbrev Values := Nat → Nat

/-- The fixed unused register prefix produced by bootstrap. -/
def junk : List Nat := List.replicate 132 0 ++ 1 :: List.replicate 58 0

/-- There is always a register before the active file, as required by the
 returning increment/decrement scans. -/
theorem junk_nonempty (A : List Nat) : junk ++ A ≠ [] := by
  intro h
  have := congrArg List.length h
  simp only [List.length_append, List.length_replicate, List.length_cons,
    List.length_nil, junk] at this
  omega

/-- Values in descending physical-address order over a finite interval. -/
def registers (R : Values) (lo n : Nat) : List Nat :=
  ((List.range' lo n).reverse).map R

/-- Expose the lowest-address register of a nonempty interval. -/
theorem registers_low (R : Values) (lo n : Nat) :
    registers R lo (n+1) = registers R (lo+1) n ++ [R lo] := by
  simp [registers, List.range'_succ, List.reverse_cons]

/-- Expose the highest-address register of an initial interval. -/
theorem registers_high (R : Values) (n : Nat) :
    registers R 0 (n+1) = R n :: registers R 0 n := by
  unfold registers
  rw [← List.range'_append_1]
  simp

/-- Adjacent address intervals concatenate in reverse order on the tape. -/
theorem registers_split (R : Values) (a b : Nat) :
    registers R 0 (a+b) = registers R a b ++ registers R 0 a := by
  unfold registers
  rw [← List.range'_append_1]
  simp

/-- Equal values on an address interval have identical unary encodings. -/
theorem registers_ext (R S : Values) (lo n : Nat)
    (h : ∀ x, lo ≤ x → x < lo+n → R x = S x) :
    registers R lo n = registers S lo n := by
  apply List.map_congr_left
  intro x hx
  simp only [List.mem_reverse, List.mem_range'] at hx
  obtain ⟨i, hi, rfl⟩ := hx
  apply h <;> omega

/-- Updating one value changes precisely its entry in the physical file. -/
theorem registers_update (R : Values) (r v : Nat) (hr : r ≤ 9) :
    junk ++ registers R (r+1) (9-r) ++ v :: registers R 0 r =
      junk ++ registers (Function.update R r v) 0 10 := by
  have heq : 10 = (r+1)+(9-r) := by omega
  rw [heq, registers_split, registers_high]
  have hhi : registers (Function.update R r v) (r+1) (9-r) =
      registers R (r+1) (9-r) := by
    apply registers_ext
    intro x hlo hhi
    exact Function.update_of_ne (by omega) _ _
  have hlo : registers (Function.update R r v) 0 r = registers R 0 r := by
    apply registers_ext
    intro x hlo hhi
    exact Function.update_of_ne (by omega) _ _
  simp [hhi, hlo, List.append_assoc]

/-- Without an update, the same decomposition reconstructs the file. -/
theorem registers_same (R : Values) (r : Nat) (hr : r ≤ 9) :
    junk ++ registers R (r+1) (9-r) ++ R r :: registers R 0 r =
      junk ++ registers R 0 10 := by
  have heq : 10 = (r+1)+(9-r) := by omega
  rw [heq, registers_split, registers_high, List.append_assoc]

/-- A dispatch boundary after `j` selector passes. The double separator lies
 between addresses `j` and `j-1`; at `j=0` it lies after the whole file. -/
def boundary (P : List Bool) (j g : Nat) (R : Values) : Zipper 308 :=
  zc root [true] (P ++ ones j ++ zeros g ++
    sepsR (junk ++ registers R j (10-j)) ++ false :: sepsR (registers R 0 j) ++ [false])

/-- Trailing blank cells do not affect the infinite tape. -/
theorem boundary_no_padding (P : List Bool) (j g : Nat) (R : Values) :
    boundary P j g R = zc root [true] (P ++ ones j ++ zeros g ++
      sepsR (junk ++ registers R j (10-j)) ++ false :: sepsR (registers R 0 j)) := by
  unfold boundary
  exact zc_padr _ _ _ 1

/-- At a completed instruction boundary the selector is invisible in the
 infinite blank suffix, leaving the ordinary unary register file. -/
theorem boundary_zero (P : List Bool) (g : Nat) (R : Values) :
    boundary P 0 g R = zc root [true] (P ++ zeros g ++ sepsR (junk ++ registers R 0 10)) := by
  rw [boundary_no_padding]
  simpa only [ones, List.replicate_zero, List.append_nil, registers, List.range'_zero,
    List.reverse_nil, List.map_nil, sepsR_nil, List.nil_append, Nat.sub_zero,
    List.append_assoc, zeros, List.replicate_succ] using
    (zc_padr root [true] (P ++ zeros g ++ sepsR (junk ++ registers R 0 10)) 1)

/-- The right-facing register file always begins with a separator, even when
 its finite list of registers is empty and only the final blank remains. -/
theorem sepsR_pad (C : List Nat) :
    sepsR C ++ [false] = false :: (sepsR C ++ [false]).tail := by
  cases C <;> rfl

/-- Split a positive gap into its first zero and remaining cells. -/
theorem zeros_pred (g : Nat) (hg : 1 ≤ g) : zeros g = false :: zeros (g-1) := by
  cases g with
  | zero => omega
  | succ g => rfl

/-- Incrementing past selector marks clears them into reusable gap zeros. -/
theorem incRev_ones (j : Nat) (U : List Bool) :
    incRev (ones j ++ U) = zeros j ++ incRev U := by
  induction j with
  | zero => rfl
  | succ j ih => simpa only [ones, zeros, List.replicate_succ, List.cons_append, incRev] using congrArg (List.cons false) ih

/-- A positive break ignores the selector marks when seeking zero ancestors. -/
theorem stripRev_ones (k j : Nat) (U : List Bool) :
    stripRev false (k+1) (ones j ++ U) = stripRev false (k+1) U := by
  induction j with
  | zero => rfl
  | succ j ih => exact ih

/-- One selector cycle advances the double separator by one register,
 preserving all register values and consuming one gap cell. -/
theorem select_cycle (P : List Bool) (d : Bool) (r : Fin 10)
    (path : Path root P (.reg d r)) (hnz : nz 0 P.reverse)
    (R : Values) (j g : Nat) (hj : j ≤ r.val) (hg : 3 ≤ g) :
    Progress m (boundary P j g R) (boundary P (j+1) (g-1) R) := by
  let A := junk ++ registers R (j+1) (9-j)
  let X := (sepsR (registers R 0 j) ++ [false]).tail
  have hsplit : junk ++ registers R j (10-j) = A ++ [R j] := by
    have heq : 10-j = (9-j)+1 := by omega
    simp only [heq, registers_low, A, List.append_assoc]
  have hX : false :: X = sepsR (registers R 0 j) ++ [false] :=
    (sepsR_pad _).symm
  have hgap : zeros g = false :: false :: zeros (g-2) := by
    cases g with
    | zero => omega
    | succ g => cases g with
      | zero => omega
      | succ g => rfl
  have hinput : boundary P j g R = zc root [true]
      (P ++ (ones j ++ false :: false :: zeros (g-2) ++
        sepsR (A ++ [R j]) ++ false :: false :: X)) := by
    unfold boundary
    rw [hsplit, hgap]
    simp only [List.append_eq, List.append_assoc, List.cons_append, List.nil_append]
    rw [← hX]
  rw [hinput]
  apply Progress.trans (path.to_register [true] _)
  lnorm
  apply Progress.trans (chain_sel d r.val j _ _ (by omega) hj)
  apply Progress.trans (by
    simpa only [List.append_eq, List.append_assoc, List.cons_append] using
      sel_op (false :: ones j ++ P.reverse ++ [true]) (g-2) A (R j) X (by omega))
  rw [zl_cons]
  apply Progress.prepend (moveL _ _ _ _ _ _ (by rfl))
  have hd := disp (ones j ++ P.reverse)
    (true :: false :: zeros (g-2) ++ sepsR A ++ false :: false :: ones (R j+1) ++ false :: X)
    ((nz_ones j P.reverse).mpr hnz)
  apply Exec.trans (by
    convert hd.exec using 1 <;>
      simp only [List.append_eq, List.append_assoc, List.cons_append] <;> rfl)
  refine ⟨0, ?_⟩
  unfold boundary
  have hsub : 10-(j+1) = 9-j := by omega
  have hsubg : g-1 = (g-2)+1 := by omega
  simp only [List.append_eq, List.reverse_append, List.reverse_reverse, List.reverse_replicate,
    hsub, hsubg, registers_high, sepsR_cons, List.replicate_succ, List.cons_append,
    List.append_assoc, A]
  rw [← hX]
  simp only [List.append_eq, List.append_assoc, List.cons_append, replicate_comm]
  rfl

/-- Repeating the selector cycle positions the separator at any requested
 active register. The available gap bounds every intermediate scan. -/
theorem select_cycles (P : List Bool) (d : Bool) (r : Fin 10)
    (path : Path root P (.reg d r)) (hnz : nz 0 P.reverse)
    (R : Values) (j g : Nat) (hj : j ≤ r.val+1) (hg : r.val+3 ≤ g) :
    Exec m (boundary P 0 g R) (boundary P j (g-j) R) := by
  induction j with
  | zero => simpa only [Nat.sub_zero] using Exec.refl m (boundary P 0 g R)
  | succ j ih =>
    apply Exec.trans (ih (by omega))
    simpa only [Nat.sub_sub] using
      (select_cycle P d r path hnz R j (g-j) (by omega) (by omega)).exec

/-- The ordinary next-instruction operation increments the binary path. -/
def nextPath (P : List Bool) : List Bool := (incRev P.reverse).reverse

/-- Advancing a path preserves its length. -/
@[simp] theorem nextPath_length (P : List Bool) : (nextPath P).length = P.length := by
  simp [nextPath]

/-- A break strips zero ancestors before advancing the remaining path. -/
def breakPath (k : Nat) (P : List Bool) : List Bool :=
  (incRev (stripRev false k P.reverse)).reverse

/-- After selection, increment modifies exactly one register and restores
 every selector cell to the gap. The execution consumes actual tape steps. -/
theorem increment_cycle (P : List Bool) (r : Fin 10)
    (path : Path root P (.reg false r)) (hnz : nz 0 P.reverse)
    (R : Values) (g : Nat) (hg : 2 ≤ g) :
    ∃ g', Progress m (boundary P (r.val+1) g R)
      (boundary (nextPath P) 0 g' (Function.update R r.val (R r.val+1))) ∧
      r.val+1+g ≤ g' := by
  let A := junk ++ registers R (r.val+1) (9-r.val)
  let C := registers R 0 r.val
  have hA : A ≠ [] := junk_nonempty _
  have hnz' : nz 0 (ones (r.val+1) ++ P.reverse) := (nz_ones _ _).mpr hnz
  obtain ⟨k, hk, _⟩ := break_ip (ones (r.val+1) ++ P.reverse) 0
    (false :: zeros (g-1) ++ sepsR A ++ false :: ones (R r.val+2) ++ sepsR C)
    (by omega) hnz'
  refine ⟨r.val+1+(k+g), ?_, by omega⟩
  rw [boundary_no_padding]
  have hs : 10-(r.val+1) = 9-r.val := by omega
  rw [hs, registers_high, sepsR_cons, zeros_pred g (by omega)]
  apply Progress.trans (by
    simpa only [List.append_eq, List.append_assoc, List.cons_append, ones, List.replicate_succ, A, C] using
      path.to_register [true] (ones (r.val+1) ++ false :: zeros (g-1) ++
        sepsR A ++ false :: false :: ones (R r.val+1) ++ sepsR C))
  try lnorm
  apply Progress.trans (chain_op false r.val _ _ (by omega))
  apply Progress.trans (by
    convert inc_op (ones (r.val+1) ++ P.reverse ++ [true]) (g-1) A (R r.val) (sepsR C) (by omega) hA using 1 <;>
      simp only [List.append_eq, List.append_assoc, List.cons_append, ones, List.replicate_succ, A, C] <;> rfl)
  apply Progress.trans_exec (by
    convert hk using 1 <;>
      simp only [List.append_eq, List.append_assoc, List.cons_append] <;> rfl)
  refine ⟨0, ?_⟩
  rw [boundary_zero]
  rw [← registers_update R r.val (R r.val+1) (by omega)]
  rw [stripRev_zero, incRev_ones]
  simp only [iterate, stripRev_zero, incRev_ones, List.reverse_append, List.reverse_cons,
    List.reverse_replicate, nextPath, sepsR_append, sepsR_cons,
    List.replicate_add, zeros_pred g (by omega), List.replicate_succ,
    List.append_eq, List.append_assoc, List.cons_append, List.nil_append, replicate_comm, A, C]

/-- A positive decrement updates one register and shifts the file right by
 one cell; the restored selector cells and new cell enlarge the gap. -/
theorem decrement_positive_cycle (P : List Bool) (r : Fin 10)
    (path : Path root P (.reg true r)) (hnz : nz 0 P.reverse)
    (R : Values) (g v : Nat) (hv : R r.val = v+1) (hg : 1 ≤ g) :
    ∃ g', Progress m (boundary P (r.val+1) g R)
      (boundary (nextPath P) 0 g' (Function.update R r.val v)) ∧
      r.val+1+g+1 ≤ g' := by
  let A := junk ++ registers R (r.val+1) (9-r.val)
  let C := registers R 0 r.val
  have hA : A ≠ [] := junk_nonempty _
  have hnz' : nz 0 (ones (r.val+1) ++ P.reverse) := (nz_ones _ _).mpr hnz
  obtain ⟨k, hk, _⟩ := break_ip (ones (r.val+1) ++ P.reverse) 0
    (false :: zeros ((g-1)+1) ++ sepsR (A ++ v :: C)) (by omega) hnz'
  refine ⟨r.val+1+(k+(g+1)), ?_, by omega⟩
  rw [boundary_no_padding]
  have hs : 10-(r.val+1) = 9-r.val := by omega
  rw [hs, registers_high, hv, sepsR_cons, zeros_pred g hg]
  apply Progress.trans (by
    simpa only [List.append_eq, List.append_assoc, List.cons_append, ones, List.replicate_succ, A, C] using
      path.to_register [true] (ones (r.val+1) ++ false :: zeros (g-1) ++
        sepsR A ++ false :: false :: ones (v+2) ++ sepsR C))
  try lnorm
  apply Progress.trans (chain_op true r.val _ _ (by omega))
  apply Progress.trans (by
    convert dec_pos_op (ones (r.val+1) ++ P.reverse ++ [true]) (g-1) A v C hA using 1 <;>
      simp only [List.append_eq, List.append_assoc, List.cons_append, ones, List.replicate_succ, A, C] <;> rfl)
  apply Progress.trans_exec (by
    convert hk using 1 <;>
      simp only [List.append_eq, List.append_assoc, List.cons_append] <;> rfl)
  refine ⟨0, ?_⟩
  rw [boundary_zero, ← registers_update R r.val v (by omega)]
  rw [stripRev_zero, incRev_ones]
  have hg' : g-1+1 = g := by omega
  simp only [iterate, hg', List.reverse_append, List.reverse_cons, List.reverse_replicate, nextPath,
    List.replicate_add, List.replicate_succ,
    List.append_eq, List.append_assoc, List.cons_append, List.nil_append, replicate_comm, A, C]

/-- The zero branch keeps the register zero and jumps out of its enclosing
 conditional. Erasing the unused path suffix also recovers tape space. -/
theorem decrement_zero_cycle (P : List Bool) (r : Fin 10)
    (path : Path root P (.reg true r)) (hnz : nz 0 P.reverse)
    (R : Values) (g : Nat) (hv : R r.val = 0) (hg : 1 ≤ g) :
    ∃ g', Progress m (boundary P (r.val+1) g R)
      (boundary (breakPath 1 P) 0 g' R) ∧
      P.length+r.val+1+g+1 ≤ (breakPath 1 P).length+g' := by
  let A := junk ++ registers R (r.val+1) (9-r.val)
  let C := registers R 0 r.val
  have hA : A ≠ [] := junk_nonempty _
  have hnz' : nz 0 (ones (r.val+1) ++ P.reverse) := (nz_ones _ _).mpr hnz
  obtain ⟨k, hk, hlen⟩ := break_ip (ones (r.val+1) ++ P.reverse) 1
    (false :: zeros ((g-1)+1) ++ sepsR (A ++ 0 :: C)) (by omega) hnz'
  rw [stripRev_ones] at hk hlen
  refine ⟨k+g+1, ?_, ?_⟩
  · rw [boundary_no_padding]
    have hs : 10-(r.val+1) = 9-r.val := by omega
    rw [hs, registers_high, hv, sepsR_cons, zeros_pred g hg]
    apply Progress.trans (by
      simpa only [List.append_eq, List.append_assoc, List.cons_append, ones, List.replicate_succ,
        List.replicate_zero, List.nil_append, A, C] using
        path.to_register [true] (ones (r.val+1) ++ false :: zeros (g-1) ++
          sepsR A ++ false :: false :: true :: sepsR C))
    try lnorm
    apply Progress.trans (chain_op true r.val _ _ (by omega))
    apply Progress.trans (by
      convert dec_zero_op (ones (r.val+1) ++ P.reverse ++ [true]) (g-1) A C hA using 1 <;>
        simp only [List.append_eq, List.append_assoc, List.cons_append, A, C] <;> rfl)
    apply Progress.trans_exec (by
      convert hk using 1 <;>
        simp only [List.append_eq, List.append_assoc, List.cons_append] <;> rfl)
    refine ⟨0, ?_⟩
    rw [boundary_zero, ← registers_same R r.val (by omega), hv]
    have hg' : g-1+1 = g := by omega
    simp only [iterate, hg', breakPath, List.replicate_add, List.replicate_succ,
      List.append_eq, List.append_assoc, List.cons_append, A, C]
    simp only [List.replicate_add, List.append_eq, List.append_assoc, List.cons_append,
      replicate_comm]
  · simp only [List.length_append, List.length_replicate, List.length_reverse, Nat.zero_add] at hlen
    simp only [breakPath, List.length_reverse, incRev_length]
    omega

/-- Complete increment, including all selector passes. It preserves the
 total space available between the path marker and the register file. -/
theorem increment (P : List Bool) (r : Fin 10)
    (path : Path root P (.reg false r)) (hnz : nz 0 P.reverse)
    (R : Values) (g : Nat) (hg : r.val+3 ≤ g) :
    ∃ g', Progress m (boundary P 0 g R)
      (boundary (nextPath P) 0 g' (Function.update R r.val (R r.val+1))) ∧ g ≤ g' := by
  obtain ⟨g', hop, hgap⟩ := increment_cycle P r path hnz R (g-(r.val+1)) (by omega)
  exact ⟨g', (select_cycles P false r path hnz R (r.val+1) g (by omega) hg).trans_progress hop, by omega⟩

/-- Complete positive decrement, including selection. Besides its arithmetic
 effect, it adds at least one cell of instruction-pointer space. -/
theorem decrement_positive (P : List Bool) (r : Fin 10)
    (path : Path root P (.reg true r)) (hnz : nz 0 P.reverse)
    (R : Values) (g v : Nat) (hv : R r.val = v+1) (hg : r.val+3 ≤ g) :
    ∃ g', Progress m (boundary P 0 g R)
      (boundary (nextPath P) 0 g' (Function.update R r.val v)) ∧ g+1 ≤ g' := by
  obtain ⟨g', hop, hgap⟩ := decrement_positive_cycle P r path hnz R (g-(r.val+1)) v hv (by omega)
  exact ⟨g', (select_cycles P true r path hnz R (r.val+1) g (by omega) hg).trans_progress hop, by omega⟩

/-- Complete zero decrement. The jump may shorten the path; the inequality
 includes those recovered cells and the new cell from the register shift. -/
theorem decrement_zero (P : List Bool) (r : Fin 10)
    (path : Path root P (.reg true r)) (hnz : nz 0 P.reverse)
    (R : Values) (g : Nat) (hv : R r.val = 0) (hg : r.val+3 ≤ g) :
    ∃ g', Progress m (boundary P 0 g R) (boundary (breakPath 1 P) 0 g' R) ∧
      P.length+g+1 ≤ (breakPath 1 P).length+g' := by
  obtain ⟨g', hop, hgap⟩ := decrement_zero_cycle P r path hnz R (g-(r.val+1)) hv (by omega)
  exact ⟨g', (select_cycles P true r path hnz R (r.val+1) g (by omega) hg).trans_progress hop, by omega⟩

/-- A complete break instruction preserves the register file and available
 pointer space while changing the ancestor path. -/
theorem break_cycle (P : List Bool) (k : Fin 3)
    (path : Path root P (.breakOp k)) (hnz : nz 0 P.reverse) (hk : 0 < k.val)
    (R : Values) (g : Nat) :
    ∃ g', Progress m (boundary P 0 g R) (boundary (breakPath k.val P) 0 g' R) ∧
      P.length+g ≤ (breakPath k.val P).length+g' := by
  obtain ⟨j, hop, hlen⟩ := path.to_break k hk hnz (zeros g ++ sepsR (junk ++ registers R 0 10))
  refine ⟨j+g, ?_, ?_⟩
  · simp only [boundary_zero, breakPath]
    convert hop using 1 <;>
      simp only [List.append_eq, List.append_assoc, zeros, List.replicate_add]
  · simp only [breakPath, List.length_reverse, incRev_length]
    omega

/-- A complete continue instruction preserves registers and space and
 returns to the selected loop ancestor. -/
theorem continue_cycle (P : List Bool) (k : Fin 5)
    (path : Path root P (.continueOp k)) (hnz : nz 0 P.reverse) (hk : 0 < k.val)
    (hc : k.val ≤ P.count true) (R : Values) (g : Nat) :
    ∃ g', Progress m (boundary P 0 g R)
      (boundary (stripRev true k.val P.reverse).reverse 0 g' R) ∧
      P.length+g ≤ (stripRev true k.val P.reverse).length+g' := by
  obtain ⟨j, hop, hlen⟩ := path.to_continue k hk hnz hc (zeros g ++ sepsR (junk ++ registers R 0 10))
  refine ⟨j+g, ?_, by omega⟩
  simp only [boundary_zero]
  convert hop using 1 <;>
    simp only [List.append_eq, List.append_assoc, zeros, List.replicate_add]

/-- A complete halt instruction really reaches the literal halted state. -/
theorem halt_cycle (P : List Bool) (path : Path root P .halt) (R : Values) (g : Nat) :
    ∃ z, Progress m (boundary P 0 g R) z ∧ z.state = none := by
  rw [boundary_zero]
  simpa only [List.append_eq, List.append_assoc] using
    path.to_halt [true] (zeros g ++ sepsR (junk ++ registers R 0 10))

end TinyZF.Tape.Framework
