import TinyZF.Tape.Simulation

/-! # Register-program certificates

This interface gives each instruction its arithmetic meaning and verifies its
implementation using the complete tape cycles. Program certificates also check
that successor instruction paths differ from the computed path only by blank
padding. Space is measured from the initial marker to the register file, so
shortening or extending a path never hides a loss of available tape space.
-/
namespace TinyZF.Tape.Framework

/-- Minimum free gap needed to select and operate on a register. Control
 instructions operate entirely within their existing pointer path. -/
def Operation.gap : Operation → Nat
  | .reg _ r => r.val+3
  | _ => 0

/-- Every decrement, including its zero branch, shifts the file right once. -/
def Operation.gain : Operation → Nat
  | .reg true _ => 1
  | _ => 0

/-- Arithmetic and path semantics of one dispatched instruction. `none`
 denotes the explicit halt instruction. This definition performs no tape work. -/
def Operation.after (op : Operation) (P : List Bool) (R : Values) :
    Option (List Bool × Values) :=
  match op with
  | .reg false r => some (nextPath P, Function.update R r.val (R r.val+1))
  | .reg true r => match R r.val with
    | 0 => some (breakPath 1 P, R)
    | v+1 => some (nextPath P, Function.update R r.val v)
  | .breakOp k => some (breakPath k.val P, R)
  | .continueOp k => some ((stripRev true k.val P.reverse).reverse, R)
  | .halt => none

/-- Obligations for a literal instruction path. The control restrictions
 prevent break/continue from treating the initial marker as an ancestor. -/
structure Admissible (P : List Bool) (op : Operation) : Prop where
  path : Path root P op
  zeros : nz 0 P.reverse
  control : match op with
    | .breakOp k => 0 < k.val
    | .continueOp k => 0 < k.val ∧ k.val ≤ P.count true
    | _ => True

/-- Uniform contract for every instruction kind. In the nonhalting case it
 preserves register semantics and the total space credit; in the halting case
 it reaches the literal halted state after positive finite execution. -/
theorem Admissible.execute {P op} (h : Admissible P op) (R : Values) (g : Nat)
    (hg : op.gap ≤ g) :
    match op.after P R with
    | none => ∃ z, Progress m (boundary P 0 g R) z ∧ z.state = none
    | some (Q, S) => ∃ g', Progress m (boundary P 0 g R) (boundary Q 0 g' S) ∧
        P.length+g+op.gain ≤ Q.length+g' := by
  cases op with
  | reg d r =>
    cases d with
    | false =>
      obtain ⟨g', hr, hl⟩ := increment P r h.path h.zeros R g hg
      exact ⟨g', hr, by simpa only [Operation.gain, nextPath_length, Nat.add_zero] using Nat.add_le_add_left hl P.length⟩
    | true =>
      cases hv : R r.val with
      | zero =>
        simpa only [Operation.after, hv, Operation.gain] using
          decrement_zero P r h.path h.zeros R g hv hg
      | succ v =>
        obtain ⟨g', hr, hl⟩ := decrement_positive P r h.path h.zeros R g v hv hg
        simp only [Operation.after, hv]
        exact ⟨g', hr, by simp only [Operation.gain, nextPath_length]; omega⟩
  | breakOp k =>
    simpa only [Operation.after, Operation.gain, Nat.add_zero] using
      break_cycle P k h.path h.zeros h.control R g
  | continueOp k =>
    simpa only [Operation.after, Operation.gain, Nat.add_zero, List.length_reverse] using
      continue_cycle P k h.path h.zeros h.control.1 h.control.2 R g
  | halt => exact halt_cycle P h.path R g

/-- Two paths represent the same bits when padded by zeros to a common
 length. This finite equality is an executable successor-path certificate. -/
def PadEq (P Q : List Bool) : Prop := P ++ zeros Q.length = Q ++ zeros P.length

instance (P Q : List Bool) : Decidable (PadEq P Q) := inferInstanceAs (Decidable (_ = _))

/-- Padding-equivalent paths have equal representations at any available
 total capacity covering both paths. The proof cancels a common blank suffix. -/
theorem PadEq.fill {P Q : List Bool} (h : PadEq P Q) (g : Nat)
    (hq : Q.length ≤ P.length+g) :
    P ++ zeros g = Q ++ zeros (P.length+g-Q.length) := by
  apply List.append_cancel_right (bs := zeros Q.length)
  calc
    (P ++ zeros g) ++ zeros Q.length = (P ++ zeros Q.length) ++ zeros g := by
      simp only [List.append_assoc, ← List.replicate_add, Nat.add_comm]
    _ = (Q ++ zeros P.length) ++ zeros g := congrArg (· ++ zeros g) h
    _ = (Q ++ zeros (P.length+g-Q.length)) ++ zeros Q.length := by
      simp only [List.append_assoc, ← List.replicate_add]
      rw [Nat.sub_add_cancel hq]

/-- Replacing a computed path with its certified successor representation
 preserves the complete infinite tape, not just the register values. -/
theorem PadEq.boundary {P Q : List Bool} (h : PadEq P Q) (g : Nat) (R : Values)
    (hq : Q.length ≤ P.length+g) :
    boundary P 0 g R = boundary Q 0 (P.length+g-Q.length) R := by
  simp only [boundary_zero]
  rw [h.fill g hq]

/-- A nonhalting instruction followed by a certified path representation
 change still makes positive progress and preserves its space credit. -/
theorem Admissible.execute_to {P Q op R S} (h : Admissible P op)
    (he : op.after P R = some (Q,S)) (target : List Bool) (hp : PadEq Q target)
    (g : Nat) (hg : op.gap ≤ g) (ht : target.length ≤ P.length+g+op.gain) :
    ∃ g', Progress m (boundary P 0 g R) (boundary target 0 g' S) ∧
      P.length+g+op.gain ≤ target.length+g' := by
  have hh := h.execute R g hg
  rw [he] at hh
  obtain ⟨j, hj, hc⟩ := hh
  have hcap : target.length ≤ Q.length+j := by omega
  refine ⟨Q.length+j-target.length, ?_, by omega⟩
  rw [← hp.boundary j S hcap]
  exact hj

/-- Executable certificate check for an instruction's path and control bounds. -/
def checkAdmissible (P : List Bool) (op : Operation) : Bool :=
  checkPath root P op && checkNz 0 P.reverse && match op with
    | .breakOp k => decide (0 < k.val)
    | .continueOp k => decide (0 < k.val ∧ k.val ≤ P.count true)
    | _ => true

/-- A successful local check discharges every hypothesis of the uniform
 tape-instruction contract, except the separately tracked free-space bound. -/
theorem checkAdmissible_sound (P : List Bool) (op : Operation)
    (h : checkAdmissible P op = true) : Admissible P op := by
  simp only [checkAdmissible, Bool.and_eq_true, checkNz_iff, decide_eq_true_eq] at h
  refine ⟨checkPath_sound root P op h.1.1, h.1.2, ?_⟩
  cases op <;> simpa only [decide_eq_true_eq] using h.2

/-- One instruction in a finite control-flow graph. Both successor indices
 are present; the zero successor is used only for zero-valued decrements. -/
structure Entry (n : Nat) where
  path : List Bool
  operation : Operation
  next : Fin n
  zero : Fin n

/-- A finite graph and its first instruction. The graph is certificate data,
 not a compiler correctness assumption. -/
structure Program (n : Nat) where
  entry : Fin n → Entry n
  start : Fin n

/-- Arithmetic register state, with a count of completed decrements used
 solely to establish the available tape space. -/
structure State (n : Nat) where
  pc : Fin n
  values : Values
  halted : Bool := false
  credit : Nat := 0

/-- Select the normal successor or the zero-decrement successor. -/
def Entry.target {n} (e : Entry n) (R : Values) : Fin n :=
  match e.operation with
  | .reg true r => if R r.val = 0 then e.zero else e.next
  | _ => e.next

/-- The exact primitive register interpreter for a finite graph. -/
def Program.step {n} (p : Program n) (s : State n) : State n :=
  if s.halted then s else
    let e := p.entry s.pc
    match e.operation.after e.path s.values with
    | none => { s with halted := true }
    | some (_, R) => ⟨e.target s.values, R, false, s.credit+e.operation.gain⟩

/-- Primitive execution starts with all ten active registers zero. -/
def Program.initial {n} (p : Program n) : State n := ⟨p.start, fun _ => 0, false, 0⟩

/-- Halting of the finite register graph is still unbounded halting. -/
def Program.Halts {n} (p : Program n) : Prop :=
  ∃ t, (iterate p.step t p.initial).halted = true

/-- Boolean equality checks the same finite padded paths, without building
 an intermediate propositional list-equality decision proof. -/
def checkPadding (P Q : List Bool) : Bool :=
  (P ++ zeros Q.length) == (Q ++ zeros P.length)

/-- The efficient Boolean padding check is exactly the original relation. -/
theorem checkPadding_eq (P Q : List Bool) : checkPadding P Q = decide (PadEq P Q) := by
  apply Bool.eq_iff_iff.mpr
  simp only [checkPadding, beq_iff_eq, decide_eq_true_eq, PadEq]

/-- Check both possible successor paths against the instruction arithmetic. -/
def checkRoutes {n} (p : Program n) (e : Entry n) : Bool :=
  match e.operation with
  | .reg false _ => checkPadding (nextPath e.path) (p.entry e.next).path
  | .reg true _ => checkPadding (nextPath e.path) (p.entry e.next).path &&
      checkPadding (breakPath 1 e.path) (p.entry e.zero).path
  | .breakOp k => checkPadding (breakPath k.val e.path) (p.entry e.next).path
  | .continueOp k => checkPadding (stripRev true k.val e.path.reverse).reverse (p.entry e.next).path
  | .halt => true

/-- A finite routing check proves correct successor dispatch for every
 possible register value, including both decrement branches. -/
theorem checkRoutes_sound {n} (p : Program n) (e : Entry n)
    (h : checkRoutes p e = true) (R : Values) (Q : List Bool) (S : Values)
    (he : e.operation.after e.path R = some (Q,S)) :
    PadEq Q (p.entry (e.target R)).path := by
  rcases e with ⟨P, op, next, zero⟩
  cases op with
  | reg d r =>
    cases d with
    | false =>
      simp only [Operation.after, Option.some.injEq, Prod.mk.injEq] at he
      simpa only [Entry.target, he.1, checkRoutes, checkPadding_eq, decide_eq_true_eq] using h
    | true =>
      simp only [checkRoutes, checkPadding_eq, Bool.and_eq_true, decide_eq_true_eq] at h
      cases hv : R r.val with
      | zero =>
        simp only [Operation.after, hv, Option.some.injEq, Prod.mk.injEq] at he
        simpa only [Entry.target, hv, ↓reduceIte, he.1] using h.2
      | succ v =>
        simp only [Operation.after, hv, Option.some.injEq, Prod.mk.injEq] at he
        simpa only [Entry.target, hv, Nat.succ_ne_zero, ↓reduceIte, he.1] using h.1
  | breakOp k =>
    simp only [Operation.after, Option.some.injEq, Prod.mk.injEq] at he
    simpa only [Entry.target, he.1, checkRoutes, checkPadding_eq, decide_eq_true_eq] using h
  | continueOp k =>
    simp only [Operation.after, Option.some.injEq, Prod.mk.injEq] at he
    simpa only [Entry.target, he.1, checkRoutes, checkPadding_eq, decide_eq_true_eq] using h
  | halt => cases he

/-- All static obligations of a program are finite and independently
 checkable: literal paths, safe dispatch, control bounds, and successor paths. -/
structure Program.Certified {n} (p : Program n) : Prop where
  instructions : ∀ i, Admissible (p.entry i).path (p.entry i).operation
  routes : ∀ i R Q S, (p.entry i).operation.after (p.entry i).path R = some (Q,S) →
    PadEq Q (p.entry ((p.entry i).target R)).path

/-- A table-wide Boolean certificate supplies the static program proof. -/
theorem Program.certified_of_check {n} (p : Program n)
    (h : ∀ i, (checkAdmissible (p.entry i).path (p.entry i).operation && checkRoutes p (p.entry i)) = true) :
    p.Certified := by
  have hi : ∀ i, checkAdmissible (p.entry i).path (p.entry i).operation = true ∧
      checkRoutes p (p.entry i) = true := by simpa only [Bool.and_eq_true] using h
  exact ⟨fun i => checkAdmissible_sound _ _ (hi i).1,
    fun i R Q S he => checkRoutes_sound p (p.entry i) (hi i).2 R Q S he⟩

/-- The currently addressed instruction fits within the initial 18 cells
 plus one cell gained by every completed decrement. -/
def Program.Fits {n} (p : Program n) (s : State n) : Prop :=
  s.halted = false → (p.entry s.pc).path.length+(p.entry s.pc).operation.gap ≤ 18+s.credit

instance {n} (p : Program n) (s : State n) : Decidable (p.Fits s) :=
  inferInstanceAs (Decidable (_ → _))

/-- Representation at an instruction boundary. Extra space is allowed:
 erased ancestor paths can give more than the guaranteed decrement credit. -/
def Program.Represents {n} (p : Program n) (z : Zipper 308) (s : State n) : Prop :=
  match s.halted with
  | true => z.state = none
  | false => ∃ g, z = boundary (p.entry s.pc).path 0 g s.values ∧
      18+s.credit ≤ (p.entry s.pc).path.length+g

/-- The representation identifies halting exactly; running boundaries
 always carry the literal instruction-root state. -/
theorem Program.Represents.halts {n} {p : Program n} {z : Zipper 308} {s : State n}
    (h : p.Represents z s) : z.state = none ↔ s.halted = true := by
  cases hs : s.halted with
  | true => simpa only [Represents, hs, iff_true] using h
  | false =>
    simp only [Represents, hs] at h
    obtain ⟨g, rfl, _⟩ := h
    simp [boundary, zc, hs]

/-- Certified instructions expand each register step into a positive finite
 run of the literal machine. Both the current and successor paths must fit. -/
theorem Program.Certified.expand {n} {p : Program n} (cert : p.Certified)
    (s : State n) (z : Zipper 308) (rep : p.Represents z s)
    (fits : p.Fits s) (fits' : p.Fits (p.step s)) :
    ∃ k, 0 < k ∧ p.Represents (iterate (Tape.step m) k z) (p.step s) := by
  cases hs : s.halted with
  | true =>
    refine ⟨1, by omega, ?_⟩
    simp only [Program.step, hs, ↓reduceIte, Represents] at rep ⊢
    simpa only [iterate] using halted_absorbing m z rep
  | false =>
    simp only [Represents, hs] at rep
    obtain ⟨g, rfl, hcredit⟩ := rep
    have hgap : (p.entry s.pc).operation.gap ≤ g := by
      have := fits hs
      omega
    cases he : (p.entry s.pc).operation.after (p.entry s.pc).path s.values with
    | none =>
      have hh := (cert.instructions s.pc).execute s.values g hgap
      rw [he] at hh
      obtain ⟨z', ⟨k, hk, hr⟩, hh⟩ := hh
      refine ⟨k, hk, ?_⟩
      simp only [Program.step, hs, ↓reduceIte, he, Represents, hr]
      exact hh
    | some result =>
      obtain ⟨Q, S⟩ := result
      have hs' : p.step s = ⟨(p.entry s.pc).target s.values, S, false,
          s.credit+(p.entry s.pc).operation.gain⟩ := by simp only [Program.step, hs, Bool.false_eq_true, ↓reduceIte, he]
      have hfit := fits' (by rw [hs'])
      rw [hs'] at hfit
      have htarget : (p.entry ((p.entry s.pc).target s.values)).path.length ≤
          (p.entry s.pc).path.length+g+(p.entry s.pc).operation.gain := by
        simp only at hfit
        omega
      obtain ⟨g', ⟨k, hk, hr⟩, hc⟩ := (cert.instructions s.pc).execute_to he
        (p.entry ((p.entry s.pc).target s.values)).path (cert.routes s.pc s.values Q S he) g hgap htarget
      refine ⟨k, hk, ?_⟩
      rw [hs', hr]
      refine ⟨g', rfl, ?_⟩
      change 18+(s.credit+(p.entry s.pc).operation.gain) ≤
        (p.entry ((p.entry s.pc).target s.values)).path.length+g'
      omega

/-- A finite instruction graph with checked paths, routing, and space bounds
 has exactly the halting behavior of the initialized binary-tape interpreter.
 The space obligation ranges over all register steps and must be proved for
 the concrete candidate; it is not inferred from a bounded test. -/
theorem Program.Certified.halts_iff {n} {p : Program n} (cert : p.Certified)
    (start : PadEq [] (p.entry p.start).path)
    (space : ∀ t, p.Fits (iterate p.step t p.initial)) :
    (∃ k, (iterate (Tape.step m) k (boundary [] 0 18 (fun _ => 0))).state = none) ↔ p.Halts := by
  let rel := fun z s => p.Represents z s ∧ ∃ t, s = iterate p.step t p.initial
  apply halting_iff_of_simulation (Tape.step m) p.step (fun z => z.state = none)
    (fun s => s.halted = true) _ p.initial rel
  · have hcap := space 0 rfl
    have hlen : (p.entry p.start).path.length ≤ 18 := by
      simp only [iterate, Program.initial] at hcap
      omega
    refine ⟨?_, 0, rfl⟩
    change ∃ g, boundary [] 0 18 (fun _ => 0) = boundary (p.entry p.start).path 0 g (fun _ => 0) ∧
      18+0 ≤ (p.entry p.start).path.length+g
    refine ⟨18-(p.entry p.start).path.length, ?_, by omega⟩
    exact start.boundary 18 (fun _ => 0) hlen
  · exact halted_absorbing m
  · intro z s h
    exact h.1.halts
  · intro z s h
    obtain ⟨t, rfl⟩ := h.2
    have hspace' : p.Fits (p.step (iterate p.step t p.initial)) := by
      simpa only [iterate_succ_last] using space (t+1)
    obtain ⟨k, hk, hr⟩ := cert.expand _ z h.1 (space t) hspace'
    exact ⟨k, hk, hr, t+1, (iterate_succ_last p.step t p.initial).symm⟩

/-- Primitive execution never loses accumulated decrement credit. -/
theorem Program.credit_monotone {n} (p : Program n) (s : State n) :
    s.credit ≤ (p.step s).credit := by
  unfold Program.step
  split
  · exact le_rfl
  · dsimp only
    split <;> simp

/-- Credit monotonicity extends to every finite run. -/
theorem Program.credit_later {n} (p : Program n) (s : State n) (t : Nat) :
    s.credit ≤ (iterate p.step t s).credit := by
  induction t with
  | zero => exact le_rfl
  | succ t ih =>
    rw [iterate_succ_last]
    exact ih.trans (p.credit_monotone _)

/-- A checked startup prefix and a global finite instruction bound suffice
 for an unbounded space invariant. After the threshold, monotone credit alone
 covers every possible path, independently of future register values. -/
theorem Program.space_of_prefix {n} (p : Program n) (threshold bound : Nat)
    (global : ∀ i, (p.entry i).path.length+(p.entry i).operation.gap ≤ bound)
    (checkedPrefix : ∀ t, t < threshold → p.Fits (iterate p.step t p.initial))
    (enough : bound ≤ 18+(iterate p.step threshold p.initial).credit) :
    ∀ t, p.Fits (iterate p.step t p.initial) := by
  intro t
  by_cases ht : t < threshold
  · exact checkedPrefix t ht
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (by omega : threshold ≤ t)
    rw [iterate_add]
    intro _
    have hc := p.credit_later (iterate p.step threshold p.initial) j
    exact (global _).trans (enough.trans (by omega))

/-- Check a consecutive finite range of certificate rows. The offset permits
 bounded kernel checks without changing or splitting the mathematical theorem. -/
def checkRange (f : Nat → Bool) (lo count : Nat) : Bool :=
  Nat.rec true (fun k checked => checked && f (lo+k)) count

/-- Independently checked adjacent ranges combine into one certificate. -/
theorem checkRange_join (f : Nat → Bool) (lo a b : Nat)
    (ha : checkRange f lo a = true) (hb : checkRange f (lo+a) b = true) :
    checkRange f lo (a+b) = true := by
  induction b with
  | zero => simpa using ha
  | succ b ih =>
    change (checkRange f (lo+a) b && f (lo+a+b)) = true at hb
    have h : checkRange f (lo+a) b = true ∧ f (lo+a+b) = true := by
      simpa only [Bool.and_eq_true] using hb
    change (checkRange f lo (a+b) && f (lo+(a+b))) = true
    rw [ih h.1, ← Nat.add_assoc, h.2]
    rfl

/-- Check one row and the remaining range separately, keeping kernel
 reduction local even when the certificate lookup contains a large table. -/
theorem checkRange_step (f : Nat → Bool) (lo count : Nat)
    (head : f lo = true) (tail : checkRange f (lo+1) count = true) :
    checkRange f lo (count+1) = true := by
  have h : checkRange f lo 1 = true := by simpa [checkRange] using head
  simpa only [Nat.add_comm 1 count] using checkRange_join f lo 1 count h tail

/-- A successful range check certifies every individual row in that range. -/
theorem checkRange_sound {f : Nat → Bool} {lo count : Nat}
    (h : checkRange f lo count = true) (i : Nat) (hl : lo ≤ i) (hi : i < lo+count) :
    f i = true := by
  induction count with
  | zero => omega
  | succ count ih =>
    change (checkRange f lo count && f (lo+count)) = true at h
    have hh : checkRange f lo count = true ∧ f (lo+count) = true := by
      simpa only [Bool.and_eq_true] using h
    by_cases he : i = lo+count
    · simpa only [he] using hh.2
    · exact ih hh.1 (by omega)

end TinyZF.Tape.Framework
