import TinyZF.Interpreter.Arithmetic
import TinyZF.Interpreter.Graph

/-! # Checked equivalence after reordering consecutive increments

The optimizer may move increments past increments to other registers. This
module captures exactly that freedom: a finite prefix contains only increments
and jumps, and its count for every register must agree with a common block.
Each block then executes an actual decrement or halt. That final instruction
ensures positive progress, so the unbounded halting equivalence cannot hide a
concrete halt between abstract samples.
-/
namespace TinyZF.Interpreter.Graph

/-- A literal graph prefix containing only increments and jumps. Its endpoint
 is the next test or halt, checked separately by the block certificate. -/
inductive Prefix {n} (p : Program n) : Fin n → List Nat → Fin n → Prop where
  | done (q) : Prefix p q [] q
  | inc {q r next xs stop} : p q = .inc r next → Prefix p next xs stop →
      Prefix p q (r::xs) stop
  | jump {q next xs stop} : p q = .jump next → Prefix p next xs stop →
      Prefix p q xs stop

/-- Counting a leading increment agrees with executing it before the rest. -/
theorem addCounts_cons (r : Nat) (xs : List Nat) (R : Values) :
    addCounts (r::xs) R = addCounts xs (Function.update R r (R r+1)) := by
  funext i
  by_cases hi : i = r
  · subst i; simp [addCounts, List.count_cons]; omega
  · simp [addCounts, List.count_cons, hi, Ne.symm hi]

/-- A checked straight-line prefix executes its complete increment multiset,
 preserving every other value. The original ordering remains in the witness. -/
theorem Prefix.run {n} {p : Program n} {q xs stop} (h : Prefix p q xs stop) (R : Values) :
    Exec p ⟨some q,R⟩ ⟨some stop,addCounts xs R⟩ := by
  induction h generalizing R with
  | done q =>
    have he : addCounts [] R = R := by funext i; simp [addCounts]
    rw [he]
    exact .refl _ _
  | inc edge rest ih =>
    rw [addCounts_cons]
    exact (Exec.single (by simp [step, edge])).trans (ih _)
  | jump edge rest ih => exact (Exec.single (by simp [step, edge])).trans (ih R)

/-- A normalized block ends in one zero-testing decrement or one halt. -/
inductive Branch (n : Nat) where
  | test (register : Nat) (positive zero : Fin n)
  | halt
  deriving DecidableEq

/-- A block records the increment multiset followed by its observable branch.
 Different concrete graphs may execute the increments in different orders. -/
structure Block (n : Nat) where
  increments : List Nat
  branch : Branch n

/-- The common intermediate graph used to compare two layouts. -/
abbrev Blocks (n : Nat) := Fin n → Block n

/-- One normalized step includes both the increment prefix and the final
 primitive test or halt. Halted states remain absorbing. -/
def blockStep {n} (p : Blocks n) (s : State n) : State n :=
  match s.pc with
  | none => s
  | some q =>
    let b := p q
    let R := addCounts b.increments s.values
    match b.branch with
    | .test r positive zero => match R r with
      | 0 => ⟨some zero,R⟩
      | v+1 => ⟨some positive,Function.update R r v⟩
    | .halt => ⟨none,R⟩

/-- Embed common block boundaries in a concrete graph. -/
def embedState {a b} (embed : Fin a → Fin b) (s : State a) : State b :=
  ⟨s.pc.map embed,s.values⟩

/-- The concrete terminal instruction must agree with the common branch and
 both successor embeddings. -/
def branchInstruction {a b} (embed : Fin a → Fin b) : Branch a → Instruction b
  | .test r positive zero => .dec r (embed positive) (embed zero)
  | .halt => .halt

/-- Each block has an actual finite increment/jump prefix, equal increment
 counts for every register, and the prescribed literal final instruction.
 These are certificate obligations, not assumed optimizer correctness. -/
structure CertifiedBlocks {a b} (p : Program b) (common : Blocks a) (embed : Fin a → Fin b) : Prop where
  block : ∀ q, ∃ xs stop, Prefix p (embed q) xs stop ∧
    (∀ r, xs.count r = (common q).increments.count r) ∧
    p stop = branchInstruction embed (common q).branch

/-- Equal register counts make two increment orders extensionally identical. -/
theorem addCounts_congr (xs ys : List Nat) (h : ∀ r, xs.count r = ys.count r) (R : Values) :
    addCounts xs R = addCounts ys R := by
  funext i
  exact congrArg (R i + ·) (h i)

/-- A certified block expands into a positive finite run of its concrete
 graph. Positivity comes from its final decrement or halt, even if the prefix
 is empty. -/
theorem CertifiedBlocks.expand {a b} {p : Program b} {common : Blocks a}
    {embed : Fin a → Fin b} (cert : CertifiedBlocks p common embed) (s : State a) :
    ∃ k, 0 < k ∧ iterate (step p) k (embedState embed s) = embedState embed (blockStep common s) := by
  rcases s with ⟨pc,R⟩
  cases pc with
  | none => exact ⟨1, by omega, rfl⟩
  | some q =>
    obtain ⟨xs, stop, walk, counts, terminal⟩ := cert.block q
    obtain ⟨k, hk⟩ := walk.run R
    rw [addCounts_congr _ _ counts] at hk
    refine ⟨k+1, by omega, ?_⟩
    rw [iterate_add]
    change step p (iterate (step p) k ⟨some (embed q),R⟩) = _
    rw [hk]
    cases hb : (common q).branch with
    | halt =>
      simp [step, terminal, hb, branchInstruction, blockStep, embedState]
    | test r positive zero =>
      cases hv : addCounts (common q).increments R r <;>
        simp [step, terminal, hb, branchInstruction, blockStep, embedState, hv]

/-- Unbounded halting of a common block graph from zero-valued registers. -/
def Blocks.Halts {n} (p : Blocks n) (entry : Fin n) : Prop :=
  ∃ k, (iterate (blockStep p) k ⟨some entry,fun _ => 0⟩).pc = none

/-- The block certificate preserves and reflects all unbounded halting, not
 merely executions up to the certificate size or a supplied time limit. -/
theorem CertifiedBlocks.halts_iff {a b} {p : Program b} {common : Blocks a}
    {embed : Fin a → Fin b} (cert : CertifiedBlocks p common embed) (entry : Fin a) :
    Halts p (embed entry) ↔ common.Halts entry := by
  apply Tape.halting_iff_of_simulation (step p) (blockStep common)
    (fun s => s.pc = none) (fun s => s.pc = none)
    ⟨some (embed entry),fun _ => 0⟩ ⟨some entry,fun _ => 0⟩
    (fun concrete abstract => concrete = embedState embed abstract)
  · rfl
  · intro s hs
    simp [step, hs]
  · intro s t h
    subst s
    simp [embedState]
  · intro s t h
    subst s
    exact cert.expand t

/-- Check an explicitly supplied sequence of successor addresses. Using
 addresses from the witness keeps each graph lookup local; no generated address
 is trusted unless the literal preceding instruction names it. -/
def checkPrefix {n} (p : Program n) (q : Fin n) (xs : List Nat)
    (successors : List (Fin n)) (stop : Fin n) : Bool :=
  match successors with
  | [] => decide (q = stop ∧ xs = [])
  | next::tail => match p q with
    | .inc r target => match xs with
      | [] => false
      | first::rest => decide (r = first ∧ target = next) && checkPrefix p next rest tail stop
    | .jump target => decide (target = next) && checkPrefix p next xs tail stop
    | _ => false

/-- The executable prefix checker yields an actual primitive-path proof. -/
theorem checkPrefix_sound {n} (p : Program n) (q : Fin n) (xs : List Nat)
    (successors : List (Fin n)) (stop : Fin n)
    (h : checkPrefix p q xs successors stop = true) : Prefix p q xs stop := by
  induction successors generalizing q xs with
  | nil =>
    simp only [checkPrefix, decide_eq_true_eq] at h
    rcases h with ⟨rfl,rfl⟩
    exact .done _
  | cons next tail ih =>
    cases hp : p q with
    | inc r target =>
      cases xs with
      | nil => simp [checkPrefix, hp] at h
      | cons first rest =>
        simp only [checkPrefix, hp, Bool.and_eq_true, decide_eq_true_eq] at h
        rcases h with ⟨⟨rfl,rfl⟩,hr⟩
        exact .inc hp (ih _ _ hr)
    | jump target =>
      simp only [checkPrefix, hp, Bool.and_eq_true, decide_eq_true_eq] at h
      rcases h with ⟨rfl,hr⟩
      exact .jump hp (ih _ _ hr)
    | dec r positive zero => simp [checkPrefix, hp] at h
    | halt => simp [checkPrefix, hp] at h

/-- Proposed finite evidence for one normalized block. Its increment order
 and all intermediate addresses are checked, not inferred from optimizer logs. -/
structure BlockWitness (n : Nat) where
  increments : List Nat
  successors : List (Fin n)
  stop : Fin n

/-- The block checker verifies the literal prefix, equal increment counts,
 and the exact branch or halt including every target address. -/
def checkBlock {a b} (p : Program b) (common : Blocks a) (embed : Fin a → Fin b)
    (q : Fin a) (w : BlockWitness b) : Bool :=
  checkPrefix p (embed q) w.increments w.successors w.stop &&
    decide (w.increments.Perm (common q).increments) &&
    decide (p w.stop = branchInstruction embed (common q).branch)

/-- Passing the finite block checks supplies the progressing simulation used
 by the unbounded halting-equivalence theorem. -/
theorem certifiedBlocks_of_check {a b} (p : Program b) (common : Blocks a)
    (embed : Fin a → Fin b) (witness : Fin a → BlockWitness b)
    (h : ∀ q, checkBlock p common embed q (witness q) = true) :
    CertifiedBlocks p common embed := by
  constructor
  intro q
  have hh := h q
  simp only [checkBlock, Bool.and_eq_true, decide_eq_true_eq] at hh
  refine ⟨(witness q).increments, (witness q).stop,
    checkPrefix_sound _ _ _ _ _ hh.1.1, ?_, hh.2⟩
  intro r
  exact List.Perm.count_eq hh.1.2 r

/-- Two concrete graphs checked against the same blocks have equivalent
 halting behavior, including all reordered increment segments. -/
theorem equivalent_of_blocks {a b c} {p : Program b} {q : Program c}
    {common : Blocks a} {left : Fin a → Fin b} {right : Fin a → Fin c}
    (hp : CertifiedBlocks p common left) (hq : CertifiedBlocks q common right) (entry : Fin a) :
    Halts p (left entry) ↔ Halts q (right entry) :=
  (hp.halts_iff entry).trans (hq.halts_iff entry).symm

end TinyZF.Interpreter.Graph
