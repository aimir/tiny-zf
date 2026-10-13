import TinyZF.Source
import TinyZF.Interpretation
import TinyZF.Decoder
import TinyZF.Machine308

/-! # Tiny ZF: checked source theorem and explicit remaining machine goal

The headline below is about the numeric source enumerator. It is **not** the
full 308-state Turing-machine theorem. See `MachineCorrect` immediately below.
-/

namespace TinyZF

/-- The unbounded numeric source search finds code 1 exactly when its explicitly
defined calculus derives code 1. No compiler or tape correctness is assumed. -/
theorem source_enumerator_correct : Source.FindsTarget ↔ Source.Provable 1 :=
  Source.enumerator_correct

/-- Remaining end-to-end goal for the literal checked-in 308-state machine.
This is a proposition definition, not a proved theorem or an assumed axiom. -/
def MachineCorrect : Prop := Machine308.Halts ↔ Source.Provable 1

/-!
Read the statement's definitions in this order:

* `Source.Provable` (`TinyZF/Source.lean`): default code 0, the exact 15 guarded
  axiom-producing schemas, detachment, and generalization.
* `Source.FindsTarget` (same file): code 1 occurs after a positive number of
  source-enumerator iterations, starting with all persistent registers zero.
* `searchStep` and `decodeInstruction` (`TinyZF/Enumeration.lean`): the actual
  `param1,param3,param2,axiomcode` wire order and exhaustive counter/tail search.
* `Source.schema` (`TinyZF/Schemas.lean`): complete guarded, permuted and
  rewritten source instances, regenerated from the current candidate.
* `Source.decode_one` (`TinyZF/Formulas.lean`): code 1 means `v₀ ∈ v₀`.
* `Machine308.Halts` (`TinyZF/Machine308.lean`): literal transitions on an
  all-zero, two-way infinite tape, starting at `0.boot.A`.

`MachineCorrect` still needs the source-to-register and register-to-tape
simulation proofs. Connecting the numeric source calculus to a conventional
ZF presentation is a further mathematical obligation, including the ICS
interpretation. Neither missing connection is supplied as a hypothesis to
the headline theorem.
-/

end TinyZF
