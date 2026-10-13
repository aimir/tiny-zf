import TinyZF.Interpreter.Placement

/-! # Unbounded correctness of the concrete source interpreter

The structured iteration contract and its checked graph placement yield a
positive finite graph execution for every source step. The progressing
simulation therefore preserves and reflects halting, without a time cutoff.
-/
namespace TinyZF.Interpreter.Correctness
open Graph FormulaStack

/-- Source search stops after the first instruction that produces target one. -/
def stoppedStep : Option (SearchState Source.Stack) → Option (SearchState Source.Stack)
  | none => none
  | some s =>
    let next := searchStep Source.execute s
    if next.payload.1 = 1 then none else some next

/-- The stopped source has an absorbing halt. -/
theorem stopped_none (n : Nat) : iterate stoppedStep n none = none := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

/-- Stopping after one of the first `n` instructions means that the independent
 pure source enumerator produced target one at one of those same instructions. -/
theorem stopped_spec (n : Nat) (s : SearchState Source.Stack) :
    iterate stoppedStep n (some s) = none ↔
      ∃ k, k < n ∧ (iterate (searchStep Source.execute) (k+1) s).payload.1 = 1 := by
  induction n generalizing s with
  | zero => simp [iterate]
  | succ n ih =>
    change iterate stoppedStep n (stoppedStep (some s)) = none ↔ _
    by_cases hit : (searchStep Source.execute s).payload.1 = 1
    · simp only [stoppedStep, hit, ite_true, stopped_none, true_iff]
      exact ⟨0, by omega, hit⟩
    · simp only [stoppedStep, hit, ite_false, ih]
      constructor
      · rintro ⟨k,hk,he⟩
        exact ⟨k+1, by omega, he⟩
      · rintro ⟨k,hk,he⟩
        cases k with
        | zero => exact False.elim (hit he)
        | succ k => exact ⟨k, by omega, he⟩

/-- The stopped interpreter's halting event is precisely the source theorem's
 existing `FindsTarget` proposition. -/
theorem stopped_iff : (∃ n, iterate stoppedStep n (some Source.initial) = none) ↔ Source.FindsTarget := by
  constructor
  · rintro ⟨n,hn⟩
    obtain ⟨k,_,hk⟩ := (stopped_spec n Source.initial).mp hn
    exact ⟨k,hk⟩
  · rintro ⟨k,hk⟩
    exact ⟨k+1, (stopped_spec (k+1) Source.initial).mpr ⟨k, by omega, hk⟩⟩

/-- Every source step changes proof control: it either advances the enumeration
 counter or strictly decreases the remaining proof tail. This prevents stuttering. -/
theorem source_step_ne (s : SearchState Source.Stack) : searchStep Source.execute s ≠ s := by
  intro eqn
  by_cases hz : s.remaining = 0
  · have h := congrArg SearchState.next eqn
    simp [searchStep, hz] at h
  · have h := congrArg SearchState.remaining eqn
    have bound := decode_tail_le (s.remaining-1)
    simp only [searchStep, hz, ite_false] at h
    omega

/-- At a live source boundary, the graph is at its literal loop entry with the
 same persistent data and clear scratch. Halted states need only agree on halting. -/
def Related (a : Graph.State 6741) : Option (SearchState Source.Stack) → Prop
  | none => a.pc = none
  | some s => a.pc = some SourceGraph.start ∧ ScratchFree a.values ∧ Execution.view a.values = s

/-- Each source transition expands into a positive finite run of the actual
 graph, using the complete structured-code placement certificate. -/
theorem expands (a : Graph.State 6741) (b : Option (SearchState Source.Stack)) (h : Related a b) :
    ∃ k, 0 < k ∧ Related (iterate (Graph.step SourceGraph.program) k a) (stoppedStep b) := by
  cases b with
  | none =>
    refine ⟨1, by omega, ?_⟩
    simpa [Related, stoppedStep, iterate, Graph.step, show a.pc = none from h] using h
  | some s =>
    rcases h with ⟨pc, scratch, view⟩
    obtain ⟨S, execution, scratchS, viewS⟩ := Execution.iteration_run a.values scratch
    rw [view] at execution viewS
    have run := Graph.Models.run execution Placement.models
    have initial : (⟨some SourceGraph.start,a.values⟩ : Graph.State 6741) = a := by
      cases a
      simp_all
    rw [initial] at run
    obtain ⟨k,hk⟩ := run
    have positive : 0 < k := by
      by_contra hn
      have zero : k = 0 := by omega
      subst k
      simp only [iterate] at hk
      by_cases hit : (searchStep Source.execute s).payload.1 = 1
      · simp only [hit, ite_true, Graph.finish] at hk
        have bad := congrArg Graph.State.pc hk
        simp [pc] at bad
      · simp only [hit, ite_false, Graph.finish] at hk
        have same := congrArg Graph.State.values hk
        change a.values = S at same
        have changed := viewS hit
        rw [← same, view] at changed
        exact source_step_ne s changed.symm
    refine ⟨k, positive, ?_⟩
    rw [hk]
    by_cases hit : (searchStep Source.execute s).payload.1 = 1
    · simp [stoppedStep, hit, Related, Graph.finish]
    · simpa [stoppedStep, hit, Related, Graph.finish] using And.intro scratchS (viewS hit)

/-- Unbounded halting of the checked unoptimized graph is exactly discovery
 of the target by the independent numeric source interpreter. -/
theorem graph_iff_source : Graph.Halts SourceGraph.program SourceGraph.start ↔ Source.FindsTarget := by
  have h := Tape.halting_iff_of_simulation
    (Graph.step SourceGraph.program) stoppedStep (fun a => a.pc = none) (fun b => b = none)
    (⟨some SourceGraph.start,fun _ => 0⟩ : Graph.State 6741) (some Source.initial) Related
    (by exact ⟨rfl, ⟨rfl,rfl⟩, rfl⟩)
    (by intro a ha; simp [Graph.step, ha])
    (by
      intro a b hb
      cases b with
      | none => exact iff_of_true hb rfl
      | some s => simp [show a.pc = some SourceGraph.start from hb.1])
    expands
  exact h.trans stopped_iff

end TinyZF.Interpreter.Correctness
