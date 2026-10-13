import TinyZF.Interpreter.Correctness
import TinyZF.Interpreter.Comparison
import TinyZF.Tape.Bootstrap
import TinyZF.Interpretation

/-! # The verified 308-state binary proof-search machine

The headline connects the literal blank-tape machine to the independently
specified numeric source calculus. No compiler correctness or ICS/ZF theory
interpretation is assumed. The latter mathematical connection remains separate.
-/
namespace TinyZF

/-- The literal 308-state binary machine halts on blank tape exactly when the
 independently defined numeric source calculus proves code one. Every tape,
 graph, arithmetic, decoding, clause, and enumeration layer is proved. -/
theorem machine_correct : Machine308.Halts ↔ Source.Provable 1 :=
  (Tape.halts_iff Machine308.machine Machine308.initial).trans
    ((Tape.halts_iff_after_exec Tape.Bootstrap.boundary).trans
      (Tape.Candidate.initialized_iff.trans
        (Interpreter.Comparison.candidate_iff_source.trans
          (Interpreter.Correctness.graph_iff_source.trans Source.enumerator_correct))))

/-- The source-only equivalence used as the final component of the headline. -/
theorem source_enumerator_correct : Source.FindsTarget ↔ Source.Provable 1 :=
  Source.enumerator_correct

/-- The fixed end-to-end contract, now discharged by `machine_correct`. -/
def MachineCorrect : Prop := Machine308.Halts ↔ Source.Provable 1

/-!
The statement's definitions are fixed independently of the implementation proof:

* `Machine308.Halts` (`TinyZF/Machine308.lean`): the literal 308-state table,
  starting at `0.boot.A`, with the head at zero on an all-zero, two-way infinite
  binary tape. Both absent transitions and explicit terminal targets halt.
* `Source.Provable` (`TinyZF/Source.lean`): derivations from default code 0,
  the exact 15 guarded schemas, detachment, and generalization.
* `Source.schema` (`TinyZF/Schemas.lean`): every current guard, parameter
  permutation, formula rewrite, and reversed Cantor payload is explicit.
* `Source.decode_one` (`TinyZF/Formulas.lean`): target code 1 means `v₀ ∈ v₀`.

Read `Interpreter/README.md` for the source-to-graph proof and `Tape/README.md`
for the literal tape implementation. The progressing simulations cover all
finite halting times, arbitrary natural register contents at their boundaries,
and every future iteration; no finite testing bound substitutes for an invariant.

A conventional ICS/ZF interpretation and an independence theorem under explicit
metatheoretic assumptions are separate mathematical obligations. The headline
neither asserts those results nor assumes them to prove implementation correctness.
-/
end TinyZF
