import TinyZF.Interpreter.Arithmetic
import TinyZF.Decoder

/-! # The proof decoder lowered to primitive register loops

The source decoder's sixteen arithmetic operations are implemented here using
the proved copying, clearing, and unpairing loops. Register numbers are exactly
the physical addresses used by the tape certificate. Concrete placement in the
instruction graph is still a separate obligation.
-/
namespace TinyZF.Interpreter.Decoding
open TinyZF.Decoder

/-- Physical address of each source register in the candidate's ten-register file. -/
def address : Register → Nat
  | .prooflist => 0 | .nextproof => 1 | .topwff => 2 | .wffstack => 3
  | .axiomcode => 4 | .param1 => 5 | .param2 => 6 | .param3 => 7
  | .scratch1 => 8 | .scratch2 => 9

/-- A partial inverse makes distinct source registers distinct physical locations. -/
def registerAt : Nat → Option Register
  | 0 => some .prooflist | 1 => some .nextproof | 2 => some .topwff
  | 3 => some .wffstack | 4 => some .axiomcode | 5 => some .param1
  | 6 => some .param2 | 7 => some .param3 | 8 => some .scratch1
  | 9 => some .scratch2 | _ => none

/-- Every declared source register is recovered at its physical address. -/
theorem address_inverse (r : Register) : registerAt (address r) = some r := by cases r <;> rfl

/-- Address assignment does not alias any of the ten source registers. -/
theorem address_injective : Function.Injective address := by
  intro r s h
  have hh := congrArg registerAt h
  simpa only [address_inverse, Option.some.injEq] using hh

/-- Read a physical register file using the source's named registers. -/
def read (R : Values) : Registers := fun r => R (address r)

/-- Named and physical updates agree exactly under the address assignment. -/
theorem read_update (R : Values) (r : Register) (v : Nat) :
    read (Function.update R (address r) v) = Function.update (read R) r v := by
  funext s
  by_cases h : s = r
  · subst s; simp [read]
  · simp [read, h, show address s ≠ address r from fun he => h (address_injective he)]

/-- Register-separation obligations required by the destructive arithmetic routines. -/
def Valid : Operation → Prop
  | .clear _ => True
  | .move source destination => source ≠ destination
  | .split head tail source => source ≠ head ∧ source ≠ tail ∧ head ≠ tail

instance (op : Operation) : Decidable (Valid op) := by cases op <;> unfold Valid <;> infer_instance

/-- Lower one arithmetic decoder instruction to actual increment/decrement loops. -/
def lower : Operation → Code
  | .clear r => clear (address r)
  | .move source destination => move (address source) [address destination]
  | .split head tail source => unpairCode (address source) (address head) (address tail)

/-- Complete physical-file postcondition of one decoder operation. -/
def after (op : Operation) (R : Values) : Values :=
  match op with
  | .clear r => Function.update R (address r) 0
  | .move source destination =>
    Function.update (Function.update R (address source) 0) (address destination)
      (R (address destination)+R (address source))
  | .split head tail source => unpaired (address source) (address head) (address tail) R

/-- Every well-separated decoder operation terminates with the exact full
 register-file effect, by the primitive arithmetic loop proofs. -/
theorem lower_run (op : Operation) (h : Valid op) (R : Values) :
    Run (lower op) R .normal (after op R) := by
  cases op with
  | clear r => exact clear_run _ R
  | move source destination =>
    exact move_one_run _ _ (fun he => h (address_injective he)) R
  | split head tail source =>
    exact unpair_run _ _ _ (fun he => h.1 (address_injective he))
      (fun he => h.2.1 (address_injective he)) (fun he => h.2.2 (address_injective he)) R

/-- The physical operation realizes the existing abstract decoder contract,
 including its specified nonzero-destination behavior. -/
theorem read_after (op : Operation) (h : Valid op) (R : Values) :
    read (after op R) = TinyZF.Decoder.apply op (read R) := by
  cases op with
  | clear r => exact read_update R r 0
  | move source destination =>
    simp only [after, read_update, TinyZF.Decoder.apply, read]
    funext r
    by_cases hr : r = source
    · subst r; simp [show source ≠ destination from h]
    · by_cases hd : r = destination
      · subst r; simp [Ne.symm h]
      · simp [hr, hd]
  | split head tail source =>
    simp only [after, unpaired, read_update, TinyZF.Decoder.apply, read]

/-- Lower a list of decoder operations in their original order. -/
def lowerList (ops : List Operation) : Code := sequence (ops.map lower)

/-- The exact physical state after a finite decoder operation list. -/
def afterList (ops : List Operation) (R : Values) : Values :=
  ops.foldl (fun V op => after op V) R

/-- Composing the primitive loop proofs implements the complete operation list. -/
theorem lowerList_run (ops : List Operation) (valid : ∀ op ∈ ops, Valid op) (R : Values) :
    Run (lowerList ops) R .normal (afterList ops R) := by
  induction ops generalizing R with
  | nil => exact .skip R
  | cons op ops ih =>
    exact .seq (lower_run op (valid op (by simp)) R)
      (ih (fun x hx => valid x (by simp [hx])) (after op R))

/-- Physical decoding and named-register decoding agree after the entire list. -/
theorem read_afterList (ops : List Operation) (valid : ∀ op ∈ ops, Valid op) (R : Values) :
    read (afterList ops R) = TinyZF.Decoder.run ops (read R) := by
  induction ops generalizing R with
  | nil => rfl
  | cons op ops ih =>
    change read (afterList ops (after op R)) = _
    rw [ih (fun x hx => valid x (by simp [hx])), read_after op (valid op (by simp))]
    rfl

/-- All sixteen recorded operations meet the arithmetic separation conditions. -/
theorem plan_valid : ∀ op ∈ TinyZF.Decoder.plan, Valid op := by
  have h : TinyZF.Decoder.plan.all (fun op => decide (Valid op)) = true := by decide +kernel
  intro op hm
  have hv := List.all_eq_true.mp h op hm
  simpa only [decide_eq_true_eq] using hv

/-- The actual sixteen-operation plan, implemented as primitive loops, decodes
 the four fields, clears both scratches, and preserves the theorem stack and
 enumeration counter exactly as specified by the existing source contract. -/
theorem decoder_run (R : Values) (h1 : R 8 = 0) (h2 : R 9 = 0) :
    ∃ S, Run (lowerList TinyZF.Decoder.plan) R .normal S ∧
      read S = TinyZF.Decoder.expected (read R) := by
  refine ⟨afterList TinyZF.Decoder.plan R, lowerList_run _ plan_valid R, ?_⟩
  rw [read_afterList _ plan_valid]
  exact TinyZF.Decoder.boundary_correct (read R) h1 h2

/-- Consume a proof-list successor, or start the next enumerated proof and
 increment the enumeration counter when the old proof list is empty. -/
def enumerationPrefix : Code :=
  .ifDec 0 .skip (.seq (move 1 [8,0]) (.seq (move 8 [1]) (.inc 1)))

/-- Exact full-file state after the enumeration prefix. -/
def enumerationAfter (R : Values) : Values :=
  if R 0 = 0 then Function.update (Function.update R 0 (R 1)) 1 (R 1+1)
  else Function.update R 0 (R 0-1)

/-- The enumeration prefix is implemented by primitive loops. It needs one
 zero scratch register and restores it; all theorem data are preserved. -/
theorem enumeration_run (R : Values) (scratch : R 8 = 0) :
    Run enumerationPrefix R .normal (enumerationAfter R) := by
  cases h0 : R 0 with
  | zero =>
    let V := transferred 1 [8,0] R
    let W := Function.update (Function.update V 8 0) 1 (V 1+V 8)
    have h : Run enumerationPrefix R .normal (Function.update W 1 (W 1+1)) :=
      .ifZero h0 (.seq (move_run 1 [8,0] (by decide) R)
        (.seq (move_one_run 8 1 (by decide) V) (.inc 1 W)))
    convert h using 1
    funext i
    by_cases hi0 : i = 0 <;> by_cases hi1 : i = 1 <;> by_cases hi8 : i = 8 <;>
      simp_all [enumerationAfter, V, W, transferred, List.count_cons] <;> omega
  | succ v =>
    have h : Run enumerationPrefix R .normal (Function.update R 0 v) := .ifPositive h0 (.skip _)
    simpa only [enumerationAfter, h0, Nat.succ_ne_zero, ite_false, Nat.add_sub_cancel] using h

/-- Enumeration and the complete decoder compose into the source instruction
 preparation phase, preserving its stack and counter specification. -/
theorem prepare_run (R : Values) (h1 : R 8 = 0) (h2 : R 9 = 0) :
    ∃ S, Run (.seq enumerationPrefix (lowerList TinyZF.Decoder.plan)) R .normal S ∧
      read S = TinyZF.Decoder.expected (read (enumerationAfter R)) := by
  have hs1 : enumerationAfter R 8 = 0 := by unfold enumerationAfter; split <;> simp [h1]
  have hs2 : enumerationAfter R 9 = 0 := by unfold enumerationAfter; split <;> simp [h2]
  obtain ⟨S, hr, he⟩ := decoder_run (enumerationAfter R) hs1 hs2
  exact ⟨S, .seq (enumeration_run R h1) hr, he⟩

end TinyZF.Interpreter.Decoding
