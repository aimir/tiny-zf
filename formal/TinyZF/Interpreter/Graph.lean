import TinyZF.Interpreter.Structured
import TinyZF.Tape.Program

/-! # Connecting structured arithmetic to finite instruction graphs

The graph language has the same individual register operations as the tape
certificate. `Models` checks a structured command's actual entries, branches,
loop back-edges, and exits. Its execution theorem is the reusable bridge from
arithmetic loop proofs to unbounded graph execution. A concrete graph still
has to provide these structural certificates.
-/
namespace TinyZF.Interpreter.Graph

/-- A graph instruction performs at most one primitive register operation. -/
inductive Instruction (n : Nat) where
  | inc (register : Nat) (next : Fin n)
  | dec (register : Nat) (positive zero : Fin n)
  | jump (next : Fin n)
  | halt
  deriving DecidableEq

/-- A finite program is a total instruction table. -/
abbrev Program (n : Nat) := Fin n → Instruction n

/-- A missing program counter is the absorbing halted state. -/
structure State (n : Nat) where
  pc : Option (Fin n)
  values : Values

/-- Exact small-step semantics, with no compound arithmetic instructions. -/
def step {n} (p : Program n) (s : State n) : State n :=
  match s.pc with
  | none => s
  | some q => match p q with
    | .inc r next => ⟨some next, Function.update s.values r (s.values r+1)⟩
    | .dec r positive zero => match s.values r with
      | 0 => ⟨some zero, s.values⟩
      | v+1 => ⟨some positive, Function.update s.values r v⟩
    | .jump next => ⟨some next, s.values⟩
    | .halt => ⟨none, s.values⟩

/-- Finite graph execution; zero steps are allowed for an empty command. -/
def Exec {n} (p : Program n) (a b : State n) : Prop :=
  ∃ k, iterate (step p) k a = b

/-- An empty sequence does not change the state. -/
theorem Exec.refl {n} (p : Program n) (a : State n) : Exec p a a := ⟨0,rfl⟩

/-- A checked primitive step is a finite graph execution. -/
theorem Exec.single {n} {p : Program n} {a b : State n} (h : step p a = b) : Exec p a b :=
  ⟨1,h⟩

/-- Finite graph executions concatenate without a time bound. -/
theorem Exec.trans {n} {p : Program n} {a b c : State n}
    (h : Exec p a b) (g : Exec p b c) : Exec p a c := by
  obtain ⟨i,hi⟩ := h
  obtain ⟨j,hj⟩ := g
  exact ⟨i+j, by rw [iterate_add, hi, hj]⟩

/-- A finite path of control-only jumps, used to place an empty command
 at a real graph boundary without inventing a register instruction. -/
inductive Jumps {n} (p : Program n) : Fin n → Fin n → Prop where
  | done (q) : Jumps p q q
  | next {q r stop} : p q = .jump r → Jumps p r stop → Jumps p q stop

/-- Certified control-only paths preserve the entire register file. -/
theorem Jumps.run {n} {p : Program n} {q stop} (h : Jumps p q stop) (R : Values) :
    Exec p ⟨some q,R⟩ ⟨some stop,R⟩ := by
  induction h with
  | done => exact .refl _ _
  | next edge rest ih => exact (Exec.single (by simp [step, edge])).trans ih

/-- Check each proposed control-only edge against the graph. -/
def checkJumps {n} (p : Program n) (q : Fin n) (successors : List (Fin n)) (stop : Fin n) : Bool :=
  match successors with
  | [] => decide (q = stop)
  | next::tail => decide (p q = .jump next) && checkJumps p next tail stop

/-- Successful finite jump checks supply the empty-command placement proof. -/
theorem checkJumps_sound {n} (p : Program n) (q : Fin n) (successors : List (Fin n)) (stop : Fin n)
    (h : checkJumps p q successors stop = true) : Jumps p q stop := by
  induction successors generalizing q with
  | nil =>
    simp only [checkJumps, decide_eq_true_eq] at h
    subst q
    exact .done _
  | cons next tail ih =>
    simp only [checkJumps, Bool.and_eq_true, decide_eq_true_eq] at h
    exact .next h.1 (ih _ h.2)

/-- Entering a loop pushes its normal exit onto the break destinations. -/
def push {n} (q : Fin n) (outer : Nat → Fin n) : Nat → Fin n
  | 0 => q
  | k+1 => outer k

/-- Interpret a structured exit as a graph state. -/
def finish {n} (x : Exit) (normal : Fin n) (breaks : Nat → Fin n) (R : Values) : State n :=
  ⟨match x with | .normal => some normal | .breakLoop k => some (breaks k) | .halt => none, R⟩

/-- A structural certificate relates source control constructs to real graph
 instructions. Loop certificates explicitly check their decrement and back-edge;
 no compiler correctness hypothesis is hidden in this relation. -/
inductive Models {n} (p : Program n) : (Nat → Fin n) → Code → Fin n → Fin n → Prop where
  | skip {breaks q next} : Jumps p q next → Models p breaks .skip q next
  | inc {breaks r q actual target next} (before : Jumps p q actual)
      (edge : p actual = .inc r target) (after : Jumps p target next) :
      Models p breaks (.inc r) q next
  | seq {breaks a b q mid next} : Models p breaks a q mid → Models p breaks b mid next →
      Models p breaks (.seq a b) q next
  | ifDec {breaks r a b q actual yes no next} (before : Jumps p q actual)
      (edge : p actual = .dec r yes no) :
      Models p breaks a yes next → Models p breaks b no next →
      Models p breaks (.ifDec r a b) q next
  | whileDec {breaks r body q actual bodyEntry zero next} (before : Jumps p q actual)
      (edge : p actual = .dec r bodyEntry zero) (afterZero : Jumps p zero next) :
      Models p (push next breaks) body bodyEntry actual → Models p breaks (.whileDec r body) q next
  | block {breaks body q next} : Models p (push next breaks) body q next →
      Models p breaks (.block body) q next
  | breakLoop {breaks k q next} (jumps : Jumps p q (breaks k)) :
      Models p breaks (.breakLoop k) q next
  | halt {breaks q actual next} (before : Jumps p q actual) (edge : p actual = .halt) :
      Models p breaks .halt q next

/-- A nonnormal exit is independent of the enclosing command's normal exit. -/
theorem finish_escape {n} {x : Exit} (h : x ≠ .normal) (a b : Fin n)
    (breaks : Nat → Fin n) (R : Values) : finish x a breaks R = finish x b breaks R := by
  cases x <;> first | contradiction | rfl

/-- Every proved structured execution expands to an actual finite graph run.
 This is valid for arbitrary natural-valued registers and all loop counts. -/
theorem Models.run {n} {p : Program n} {code R x S} (execution : Run code R x S) :
    ∀ {breaks q next}, Models p breaks code q next →
      Exec p ⟨some q,R⟩ (finish x next breaks S) := by
  induction execution with
  | skip R =>
    intro breaks q next model
    cases model with
    | skip jumps => exact jumps.run R
  | inc r R =>
    intro breaks q next model
    cases model with
    | inc before edge after =>
      exact (before.run R).trans ((Exec.single (by simp [step, edge])).trans (after.run _))
  | seq first second ihFirst ihSecond =>
    intro breaks q next model
    cases model with
    | seq left right => exact (ihFirst left).trans (ihSecond right)
  | escape first hx ih =>
    intro breaks q next model
    cases model with
    | seq left right =>
      have h := ih left
      rw [finish_escape hx _ next] at h
      exact h
  | ifPositive hr body ih =>
    intro breaks q next model
    cases model with
    | ifDec before edge left right =>
      exact (before.run _).trans ((Exec.single (by simp [step, edge, hr])).trans (ih left))
  | ifZero hr body ih =>
    intro breaks q next model
    cases model with
    | ifDec before edge left right =>
      exact (before.run _).trans ((Exec.single (by simp [step, edge, hr])).trans (ih right))
  | whileZero hr =>
    intro breaks q next model
    cases model with
    | whileDec before edge afterZero body =>
      exact (before.run _).trans ((Exec.single (by simp [step, edge, hr])).trans (afterZero.run _))
  | whileNext hr body rest ihBody ihRest =>
    intro breaks q next model
    cases model with
    | whileDec before edge afterZero bodyModel =>
      exact (before.run _).trans ((Exec.single (by simp [step, edge, hr])).trans
        ((ihBody bodyModel).trans (ihRest (.whileDec (.done _) edge afterZero bodyModel))))
  | whileBreak hr body ih =>
    intro breaks q next model
    cases model with
    | whileDec before edge afterZero bodyModel =>
      exact (before.run _).trans ((Exec.single (by simp [step, edge, hr])).trans (ih bodyModel))
  | whileOuter hr body ih =>
    intro breaks q next model
    cases model with
    | whileDec before edge afterZero bodyModel =>
      exact (before.run _).trans ((Exec.single (by simp [step, edge, hr])).trans (ih bodyModel))
  | whileHalt hr body ih =>
    intro breaks q next model
    cases model with
    | whileDec before edge afterZero bodyModel =>
      have h := ih bodyModel
      exact (before.run _).trans ((Exec.single (by simp [step, edge, hr])).trans h)
  | blockNormal body ih =>
    intro breaks q next model
    cases model with
    | block bodyModel => have h := ih bodyModel; exact h
  | blockBreak body ih =>
    intro breaks q next model
    cases model with
    | block bodyModel => have h := ih bodyModel; exact h
  | blockOuter body ih =>
    intro breaks q next model
    cases model with
    | block bodyModel => have h := ih bodyModel; exact h
  | blockHalt body ih =>
    intro breaks q next model
    cases model with
    | block bodyModel => have h := ih bodyModel; exact h
  | breakLoop k R =>
    intro breaks q next model
    cases model with
    | breakLoop jumps => exact jumps.run R
  | halt R =>
    intro breaks q next model
    cases model with
    | halt before edge => exact (before.run R).trans (Exec.single (by simp [step, edge, finish]))

/-- Erase the tape certificate's path and space bookkeeping, retaining every
 primitive register instruction and both decrement successors. -/
def ofTapeProgram {n} (p : Tape.Framework.Program n) : Program n := fun q =>
  let e := p.entry q
  match e.operation with
  | .reg false r => .inc r.val e.next
  | .reg true r => .dec r.val e.next e.zero
  | .breakOp _ | .continueOp _ => .jump e.next
  | .halt => .halt

/-- Projection discards only the proof's accumulated tape-space credit. -/
def ofTapeState {n} (s : Tape.Framework.State n) : State n :=
  ⟨if s.halted then none else some s.pc, s.values⟩

/-- Erasing bookkeeping commutes with each actual register-program step. -/
theorem ofTapeState_step {n} (p : Tape.Framework.Program n) (s : Tape.Framework.State n) :
    ofTapeState (p.step s) = step (ofTapeProgram p) (ofTapeState s) := by
  cases hs : s.halted with
  | true => simp [ofTapeState, Tape.Framework.Program.step, hs, step]
  | false =>
    cases hop : (p.entry s.pc).operation with
    | reg d r =>
      cases d with
      | false => simp [ofTapeState, Tape.Framework.Program.step, hs, step,
          ofTapeProgram, hop, Tape.Framework.Operation.after, Tape.Framework.Entry.target]
      | true =>
        cases hv : s.values r.val <;>
          simp [ofTapeState, Tape.Framework.Program.step, hs, step,
            ofTapeProgram, hop, Tape.Framework.Operation.after, Tape.Framework.Entry.target, hv]
    | breakOp k => simp [ofTapeState, Tape.Framework.Program.step, hs, step,
        ofTapeProgram, hop, Tape.Framework.Operation.after, Tape.Framework.Entry.target]
    | continueOp k => simp [ofTapeState, Tape.Framework.Program.step, hs, step,
        ofTapeProgram, hop, Tape.Framework.Operation.after, Tape.Framework.Entry.target]
    | halt => simp [ofTapeState, Tape.Framework.Program.step, hs, step,
        ofTapeProgram, hop, Tape.Framework.Operation.after]

/-- The bookkeeping projection commutes with every finite execution. -/
theorem ofTapeState_iterate {n} (p : Tape.Framework.Program n) (s : Tape.Framework.State n)
    (k : Nat) : ofTapeState (iterate p.step k s) =
      iterate (step (ofTapeProgram p)) k (ofTapeState s) := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih => rw [iterate, ih, ofTapeState_step]; rfl

/-- Halting of a graph starts with a specified entry and ten zero registers. -/
def Halts {n} (p : Program n) (entry : Fin n) : Prop :=
  ∃ k, (iterate (step p) k ⟨some entry, fun _ => 0⟩).pc = none

/-- Erasing pointer and space metadata preserves and reflects unbounded
 halting. This joins the tape certificate to the source-oriented graph API. -/
theorem ofTapeProgram_halts {n} (p : Tape.Framework.Program n) :
    Halts (ofTapeProgram p) p.start ↔ p.Halts := by
  unfold Halts Tape.Framework.Program.Halts
  apply exists_congr
  intro k
  change (iterate (step (ofTapeProgram p)) k (ofTapeState p.initial)).pc = none ↔ _
  rw [← ofTapeState_iterate]
  cases hs : (iterate p.step k p.initial).halted <;> simp [ofTapeState, hs]

end TinyZF.Interpreter.Graph
