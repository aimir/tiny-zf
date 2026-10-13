import TinyZF

/-! Exact theorem-type probes followed by their kernel axiom dependencies. -/

example : TinyZF.Machine308.Halts ↔ TinyZF.Source.Provable 1 := TinyZF.machine_correct
example : TinyZF.MachineCorrect := TinyZF.machine_correct

example : TinyZF.Source.FindsTarget ↔ TinyZF.Source.Provable 1 := TinyZF.source_enumerator_correct
example : TinyZF.MachineCorrect =
    (TinyZF.Machine308.Halts ↔ TinyZF.Source.Provable 1) := rfl
example (i : TinyZF.Instruction) (tail : Nat) :
    TinyZF.decodeInstruction (TinyZF.encodeInstruction i tail) = (i, tail) :=
  TinyZF.decode_encode i tail
example (r : TinyZF.Decoder.Registers) (h1 : r .scratch1 = 0) (h2 : r .scratch2 = 0) :
    TinyZF.Decoder.run TinyZF.Decoder.plan r = TinyZF.Decoder.expected r :=
  TinyZF.Decoder.boundary_correct r h1 h2

#print axioms TinyZF.machine_correct
#print axioms TinyZF.Tape.Bootstrap.boundary
#print axioms TinyZF.Tape.Candidate.initialized_iff
#print axioms TinyZF.Interpreter.Comparison.candidate_iff_source
#print axioms TinyZF.Interpreter.Placement.models
#print axioms TinyZF.Interpreter.Execution.iteration_run
#print axioms TinyZF.Interpreter.Correctness.graph_iff_source
#print axioms TinyZF.source_enumerator_correct
#print axioms TinyZF.Source.compile
#print axioms TinyZF.Source.iteration_sound
#print axioms TinyZF.every_program_runs
#print axioms TinyZF.Cantor.tri_formula
#print axioms TinyZF.Cantor.unpair_pair
#print axioms TinyZF.Cantor.pair_unpair
#print axioms TinyZF.Decoder.boundary_correct
#print axioms TinyZF.Source.decode_code
#print axioms TinyZF.Source.code_injective
#print axioms TinyZF.Source.derivation_valid
#print axioms TinyZF.Source.protected_rewrites_correct
#print axioms TinyZF.Machine308.state_count
