import TinyZF.Enumeration

/-! # Current decoder's register allocation

This proves the 16-operation allocation plan for arbitrary register values.
Operations use arithmetic contracts; it does not assume, or prove, that the
literal tape implements those contracts.
-/
namespace TinyZF.Decoder
open Cantor

/-- The ten active registers of the 308-state candidate. -/
inductive Register where
  | prooflist | nextproof | topwff | wffstack | axiomcode
  | param1 | param2 | param3 | scratch1 | scratch2
  deriving DecidableEq, Repr

/-- Register values are unbounded natural numbers. -/
abbrev Registers := Register → Nat

/-- Decoder operations at the arithmetic contract level. -/
inductive Operation where
  | clear (r : Register)
  | move (source destination : Register)
  | split (head tail source : Register)

/-- Transfers add to their destination; unpairing walks from the old output pair.
Thus correctness cannot be obtained by silently ignoring nonzero destinations. -/
def apply (op : Operation) (r : Registers) : Registers :=
  match op with
  | .clear x => Function.update r x 0
  | .move x y => Function.update (Function.update r y (r y + r x)) x 0
  | .split x y z =>
    let value := unpair (pair (r x) (r y) + r z)
    Function.update (Function.update (Function.update r z 0) x value.1) y value.2

/-- Exact plan emitted for `candidates/ics-best.json`; checked by the import audit. -/
def plan : List Operation := [
  .split .scratch1 .scratch2 .prooflist, .move .scratch2 .prooflist,
  .clear .param1, .move .scratch1 .param1,
  .split .scratch1 .scratch2 .prooflist, .move .scratch2 .prooflist,
  .clear .param3, .move .scratch1 .param3,
  .split .scratch1 .scratch2 .prooflist, .move .scratch2 .prooflist,
  .clear .param2, .move .scratch1 .param2,
  .split .scratch1 .scratch2 .prooflist, .move .scratch2 .prooflist,
  .clear .axiomcode, .move .scratch1 .axiomcode]

/-- Execute the arithmetic contracts in order. -/
def run (ops : List Operation) (r : Registers) := ops.foldl (fun s op => apply op s) r

/-- Expected boundary: four decoded fields and remainder, cleared scratch, and
unchanged counter and theorem stack. Old parameter values may be arbitrary. -/
def expected (r : Registers) : Registers := fun reg =>
  let decoded := decodeInstruction (r .prooflist)
  match reg with
  | .prooflist => decoded.2
  | .param1 => decoded.1.p1
  | .param2 => decoded.1.p2
  | .param3 => decoded.1.p3
  | .axiomcode => decoded.1.selector
  | .scratch1 | .scratch2 => 0
  | _ => r reg

/-- The exact allocation plan satisfies the full boundary contract for every
input and arbitrary old parameters. Both scratch registers begin at zero. -/
theorem boundary_correct (r : Registers) (h1 : r .scratch1 = 0) (h2 : r .scratch2 = 0) :
    run plan r = expected r := by
  funext reg
  cases reg <;>
    simp [run, plan, apply, expected, decodeInstruction, h1, h2,
      show pair 0 0 = 0 from rfl]

end TinyZF.Decoder
