import Mathlib.Tactic

/-! # Literal binary-tape semantics

The tape is indexed by all integers. A transition writes one bit and moves one
cell. `none` as a transition means immediate halting; `next = none` means an
explicit halt after the write/move. Neither outcome is counted as a working state.
-/
namespace TinyZF

/-- One literal write, direction (`true` = right), and destination. -/
structure Transition (states : Nat) where
  write : Bool
  right : Bool
  next : Option (Fin states)
  deriving DecidableEq, Repr

/-- A finite transition table may leave a state/read pair undefined. -/
abbrev Machine (states : Nat) := Fin states → Bool → Option (Transition states)

/-- Configurations use an unbounded tape, not the finite tape of the search harness. -/
structure Configuration (states : Nat) where
  state : Option (Fin states)
  head : Int
  tape : Int → Bool

/-- One literal step; halting configurations remain halted. -/
def Machine.step {n : Nat} (m : Machine n) (c : Configuration n) : Configuration n :=
  match c.state with
  | none => c
  | some q =>
    match m q (c.tape c.head) with
    | none => { c with state := none }
    | some t => ⟨t.next, c.head + (if t.right then 1 else -1), Function.update c.tape c.head t.write⟩

/-- Any finite number of literal steps from a configuration. -/
def Machine.run {n : Nat} (m : Machine n) : Nat → Configuration n → Configuration n
  | 0, c => c
  | k + 1, c => m.run k (m.step c)

/-- Halting is reachability of a halted configuration, without a step bound. -/
def Machine.halts {n : Nat} (m : Machine n) (c : Configuration n) : Prop :=
  ∃ k, (m.run k c).state = none

/-- Once halted, the machine cannot resume; explicit and missing-transition halts agree here. -/
theorem Machine.halted_fixed {n : Nat} (m : Machine n) (c : Configuration n)
    (h : c.state = none) (k : Nat) : m.run k c = c := by
  induction k with
  | zero => rfl
  | succ k ih => simpa [Machine.run, Machine.step, h] using ih

end TinyZF
