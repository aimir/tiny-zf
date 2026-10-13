import TinyZF.Interpreter.Clauses

/-! # One complete source-interpreter iteration

This module composes the primitive-loop contracts in the fixed clause order,
including the protected boundary and final destructive test for target one.
The concrete instruction graph still needs the separate placement certificate.
-/
set_option maxHeartbeats 4000000

namespace TinyZF.Interpreter.Execution
open Cantor FormulaStack Expressions Clauses

/-- Semantically distinct stages of clause execution. -/
inductive Phase where
  | «axiom» (index : Fin 15)
  | detach | generalize | protect
  deriving DecidableEq

/-- The actual clause order; protection occurs once before the five protected schemas. -/
def phases : List Phase :=
  [.axiom 8, .axiom 5, .axiom 1, .axiom 6, .axiom 0, .axiom 2,
   .detach, .axiom 7, .axiom 3, .generalize, .axiom 9, .axiom 4,
   .protect, .axiom 14, .axiom 11, .axiom 10, .axiom 12, .axiom 13]

/-- Every phase expands into the proved primitive-loop source code. -/
def phaseCode : Phase → Code
  | .axiom k => expressionClause (SchemaCode.expression k)
  | .detach => Clauses.detach | .generalize => Clauses.generalize | .protect => Clauses.protect

/-- Full-file effect of a phase, retaining changes to temporarily live parameters. -/
def phaseAfter : Phase → Values → Values
  | .axiom k => expressionAfter (SchemaCode.expression k)
  | .detach => detached | .generalize => generalized | .protect => guarded

/-- Each phase terminates and implements its exact full-file contract. -/
theorem phase_run (p : Phase) (R : Values) (scratch : ScratchFree R) :
    Run (phaseCode p) R .normal (phaseAfter p R) := by
  cases p with
  | «axiom» k => exact expressionClause_run _ R scratch
  | detach => exact detach_run R scratch
  | generalize => exact generalize_run R scratch
  | protect => exact protect_run R scratch

/-- Every phase restores the shared zero scratch registers. -/
theorem phase_scratch (p : Phase) (R : Values) (scratch : ScratchFree R) :
    ScratchFree (phaseAfter p R) := by
  cases p with
  | «axiom» k => simpa [phaseAfter, expressionAfter, ScratchFree] using scratch
  | generalize =>
    simpa [phaseAfter, generalized, expressionAfter, ScratchFree] using
      taken_scratch 7 (by decide) (by decide) R scratch
  | detach =>
    simpa [phaseAfter, detached, ScratchFree] using
      taken_scratch 6 (by decide) (by decide) (taken 7 R)
        (taken_scratch 7 (by decide) (by decide) R scratch)
  | protect => simpa [phaseAfter, guarded, ScratchFree] using scratch

/-- A list of phases composes without imposing bounds on register values. -/
theorem phases_run (ps : List Phase) (R : Values) (scratch : ScratchFree R) :
    Run (sequence (ps.map phaseCode)) R .normal (ps.foldl (fun V p => phaseAfter p V) R) := by
  induction ps generalizing R with
  | nil => exact .skip R
  | cons p ps ih => exact .seq (phase_run p R scratch) (ih _ (phase_scratch p R scratch))

/-- The complete fixed sequence of formula-producing clauses. -/
def clauses : Code := sequence (phases.map phaseCode)

/-- Full-file result of the complete fixed sequence. -/
def clausesAfter (R : Values) : Values := phases.foldl (fun V p => phaseAfter p V) R

/-- The complete clause sequence implements its compositional register effect. -/
theorem clauses_run (R : Values) (scratch : ScratchFree R) :
    Run clauses R .normal (clausesAfter R) := phases_run phases R scratch

/-- A complete clause pass restores both scratch registers. -/
theorem clauses_scratch (R : Values) (scratch : ScratchFree R) :
    ScratchFree (clausesAfter R) := by
  have all (ps : List Phase) (V : Values) (h : ScratchFree V) :
      ScratchFree (ps.foldl (fun W p => phaseAfter p W) V) := by
    induction ps generalizing V with
    | nil => exact h
    | cons p ps ih => exact ih _ (phase_scratch p V h)
  exact all phases R scratch

/-- Clause execution preserves the enumeration registers at physical addresses
 zero and one; parameter changes remain local to the current instruction. -/
theorem clauses_frame (R : Values) (i : Nat) (hi : i < 2) :
    clausesAfter R i = R i := by
  have one (p : Phase) (V : Values) : phaseAfter p V i = V i := by
    cases p <;> simp [phaseAfter, expressionAfter, detached, generalized, guarded, taken,
      show i ≠ 2 by omega, show i ≠ 3 by omega, show i ≠ 4 by omega,
      show i ≠ 5 by omega, show i ≠ 6 by omega, show i ≠ 7 by omega]
    all_goals split_ifs <;> simp_all [show i ≠ 3 by omega, show i ≠ 6 by omega, show i ≠ 7 by omega]
  have all (ps : List Phase) (V : Values) :
      ps.foldl (fun W p => phaseAfter p W) V i = V i := by
    induction ps generalizing V with
    | nil => rfl
    | cons p ps ih => simpa only [List.foldl, one] using ih (phaseAfter p V)
  exact all phases R

/-- The full primitive clause order implements the existing source stack
 operation for every selector, including the unbounded saturated final case. -/
theorem clauses_source (R : Values) :
    let V := clausesAfter (setStack R 0 (pair (R 2) (R 3)))
    (V 2, V 3) = Source.execute ⟨R 4, R 5, R 6, R 7⟩ (R 2, R 3) := by
  by_cases small : R 4 < 17
  · generalize hs : R 4 = selector at *
    interval_cases selector <;>
      simp [clausesAfter, phases, phaseAfter, expressionAfter, generalized, detached,
        taken, guarded, setStack, parameters, eval, SchemaCode.expression,
        Source.execute, Source.dispatch, Source.schema, Source.weq, Source.wel,
        Source.wim, Source.wn, Source.wal, Source.wex, Source.wa, hs]
  · obtain ⟨d, hd⟩ : ∃ d, R 4 = d+17 := ⟨R 4-17, by omega⟩
    simp (disch := omega) [clausesAfter, phases, phaseAfter, expressionAfter, generalized,
      detached, taken, guarded, setStack, parameters, eval, SchemaCode.expression,
      Source.execute, Source.dispatch, Source.schema, Source.weq, Source.wel,
      Source.wim, Source.wn, Source.wal, Source.wex, Source.wa, hd, Nat.add_sub_assoc]

/-- The halt test consumes a top equal to one; larger positive tops are restored. -/
def haltCheck : Code := .ifDec 2 (.ifDec 2 (.seq (.inc 2) (.inc 2)) .halt) .skip

/-- The halt test exits exactly on target one, preserving the whole register
 file on every normal return. -/
theorem haltCheck_run (R : Values) :
    Run haltCheck R (if R 2 = 1 then .halt else .normal)
      (if R 2 = 1 then Function.update R 2 0 else R) := by
  cases h : R 2 with
  | zero => simpa [h, haltCheck] using (Run.ifZero (r := 2)
      (a := .ifDec 2 (.seq (.inc 2) (.inc 2)) .halt) h (Run.skip R))
  | succ n =>
    cases n with
    | zero =>
      have x : Run haltCheck R .halt (Function.update R 2 0) :=
        .ifPositive h (.ifZero (by simp) (.halt _))
      simpa [h] using x
    | succ n =>
      let U := Function.update R 2 (n+1)
      let V := Function.update U 2 n
      have body : Run (.seq (.inc 2) (.inc 2)) V .normal R := by
        convert Run.seq (Run.inc 2 V) (Run.inc 2 (Function.update V 2 (V 2+1))) using 1
        funext i
        by_cases hi : i = 2 <;> simp [U, V, hi, h]
      have x : Run haltCheck R .normal R := .ifPositive h (.ifPositive (by simp [U]) body)
      simpa [h] using x

/-- One full interpreter iteration at the primitive register-instruction level. -/
def code : Code :=
  .seq Decoding.enumerationPrefix (.seq (Decoding.lowerList TinyZF.Decoder.plan)
    (.seq push (.seq clauses haltCheck)))

/-- Persistent source state observed at an interpreter boundary. -/
def view (R : Values) : SearchState Source.Stack := ⟨R 0, R 1, (R 2, R 3)⟩

/-- The physical state after enumeration and the recorded decoder plan. -/
def prepared (R : Values) : Values :=
  Decoding.afterList TinyZF.Decoder.plan (Decoding.enumerationAfter R)

/-- The decoder's named-register contract at the prepared physical boundary. -/
theorem prepared_spec (R : Values) (scratch : ScratchFree R) :
    Decoding.read (prepared R) = TinyZF.Decoder.expected (Decoding.read (Decoding.enumerationAfter R)) := by
  unfold prepared
  rw [Decoding.read_afterList _ Decoding.plan_valid]
  apply TinyZF.Decoder.boundary_correct
  · unfold Decoding.read Decoding.address Decoding.enumerationAfter
    split <;> simp [scratch.1]
  · unfold Decoding.read Decoding.address Decoding.enumerationAfter
    split <;> simp [scratch.2]

/-- The entire normal prefix through clause selection, before testing for one. -/
def produced (R : Values) : Values :=
  let D := prepared R
  clausesAfter (setStack D 0 (pair (D 2) (D 3)))

/-- Both work registers are clear after decoding and all clauses. -/
theorem produced_scratch (R : Values) (scratch : ScratchFree R) : ScratchFree (produced R) := by
  have h := prepared_spec R scratch
  have h8 := congrFun h TinyZF.Decoder.Register.scratch1
  have h9 := congrFun h TinyZF.Decoder.Register.scratch2
  apply clauses_scratch
  apply scratch_setStack
  exact ⟨h8,h9⟩

/-- A full primitive prefix implements one step of the independent source
 enumerator, including proof-tail selection, decoding, and theorem-stack effects. -/
theorem produced_view (R : Values) (scratch : ScratchFree R) :
    view (produced R) = searchStep Source.execute (view R) := by
  let D := prepared R
  let E := Decoding.enumerationAfter R
  have spec := prepared_spec R scratch
  have fields (r : TinyZF.Decoder.Register) := congrFun spec r
  have h0 := fields .prooflist
  have h1 := fields .nextproof
  have h2 := fields .topwff
  have h3 := fields .wffstack
  have h4 := fields .axiomcode
  have h5 := fields .param1
  have h6 := fields .param2
  have h7 := fields .param3
  simp only [Decoding.read, Decoding.address, TinyZF.Decoder.expected] at h0 h1 h2 h3 h4 h5 h6 h7
  have stack := clauses_source D
  change (produced R 2, produced R 3) = _ at stack
  conv at stack =>
    rhs
    dsimp only [D]
    rw [h2,h3,h4,h5,h6,h7]
  have left := clauses_frame (setStack D 0 (pair (D 2) (D 3))) 0 (by decide)
  have right := clauses_frame (setStack D 0 (pair (D 2) (D 3))) 1 (by decide)
  change produced R 0 = D 0 at left
  change produced R 1 = D 1 at right
  unfold view
  rw [left, right, stack]
  dsimp only [D]
  rw [h0,h1]
  unfold searchStep Decoding.enumerationAfter
  split_ifs <;> rfl

/-- One structured iteration terminates normally with the exact next source
 state, or halts exactly when that next state's theorem is one. -/
theorem iteration_run (R : Values) (scratch : ScratchFree R) :
    ∃ S, Run code R
      (if (searchStep Source.execute (view R)).payload.1 = 1 then .halt else .normal) S ∧
      ScratchFree S ∧
      ((searchStep Source.execute (view R)).payload.1 ≠ 1 →
        view S = searchStep Source.execute (view R)) := by
  let E := Decoding.enumerationAfter R
  let D := prepared R
  let P := setStack D 0 (pair (D 2) (D 3))
  let C := produced R
  have spec := prepared_spec R scratch
  have hd : ScratchFree D := ⟨congrFun spec .scratch1, congrFun spec .scratch2⟩
  have hc : ScratchFree C := produced_scratch R scratch
  have eqv := produced_view R scratch
  have eqtop : C 2 = (searchStep Source.execute (view R)).payload.1 := congrArg (fun s => s.payload.1) eqv
  have execution := Run.seq (Decoding.enumeration_run R scratch.1)
    (Run.seq (Decoding.lowerList_run _ Decoding.plan_valid E)
      (Run.seq (push_run D hd)
        (Run.seq (clauses_run P (scratch_setStack _ _ _ hd)) (haltCheck_run C))))
  refine ⟨if C 2 = 1 then Function.update C 2 0 else C, ?_, ?_, ?_⟩
  · simpa only [code, ← eqtop] using execution
  · split_ifs <;> simpa [ScratchFree] using hc
  · intro hn
    simpa [eqtop, hn] using eqv

end TinyZF.Interpreter.Execution
