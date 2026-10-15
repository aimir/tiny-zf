# Candidate tables

- **Shared-startup machine: 251 states**, in [mira251-startup.tm](mira251-startup.tm),
  with its [203-node decoder tree](mira251-startup.tree.json) and
  [Coq verification record](../reference/mira251-startup-coq.json). It removes a
  startup state from the 252-state machine and reaches the source enumerator's
  third state. Complete blank-tape halting equivalence to ZF/ZFC inconsistency.
  [Reproduce the artifacts and proof](../formal/coq/README.md#verify-a-changed-machine).

- **Local-carry machine: 252 states**, in [mira252-local.tm](mira252-local.tm),
  with its [203-node decoder tree](mira252-local.tree.json) and
  [Coq verification record](../reference/mira252-local-coq.json). A two-state
  gap-carry loop saves two states over the pinned 254-state machine. Complete
  blank-tape halting equivalence to conventional ZF/ZFC inconsistency.
  [Reproduce the artifacts and proof](../formal/coq/README.md#verify-a-changed-machine).

- **Forward-decrement machine: 253 states**, in [mira253-forward.tm](mira253-forward.tm),
  with its [203-node decoder tree](mira253-forward.tree.json) and
  [Coq verification record](../reference/mira253-forward-coq.json). A new register
  decrement kernel saves one state while preserving the source interpreter.
  Complete blank-tape halting equivalence to conventional ZF/ZFC inconsistency.
  [Reproduce the artifacts and proof](../formal/coq/README.md#verify-a-changed-machine).
- **Mira-based variant: 254 states**, in [mira254-rotation.tm](mira254-rotation.tm),
  with its [exact decoder tree](mira254-rotation.tree.json) and
  [Coq verification record](../reference/mira254-rotation-coq.json). Complete
  blank-tape halting equivalence to conventional ZF/ZFC inconsistency. This
  matches Mira-Cult's state count. [Rebuild the proof](../formal/coq/README.md#verify-a-changed-machine).
- **ICS candidate: 308 states**, in [ics-best.tm](ics-best.tm), with
  [configuration and hashes](ics-best.json) and the [instruction tree](ics-tree.json).
  The Lean headline proves that this exact binary machine halts on blank tape
  iff its numeric source calculus derives code 1. The calculus-to-ZF bridge
  remains outside that theorem. Run `python3 tools/verify_ics.py` for the
  computational checks and follow the [Lean guide](../formal/README.md) for
  formal verification.
- **Conservative baseline: 392 states**, in [best.tm](best.tm), with
  [configuration](best.json). Retains all distinct Wade axiom clauses. Run
  `python3 tools/verify.py`. This table has no end-to-end formal proof here.

All tables start on a blank two-way binary tape. The 251-state table has working
states 0 through 250 and undefined terminal state 251. The 252-state table has working states 0 through 251 and undefined terminal
state 252. The 253-state table has working
states 0 through 252 and undefined terminal state 253; the 254-state table uses
working states 0 through 253 and undefined terminal state 254. The ICS and Wade tables retain
the upstream named partial-transition format. No post-compilation reduction is
needed for their advertised counts.

The 392-state baseline avoids the ICS theory/encoding changes, making it a useful
comparison. The 308-state Lean machine and 251-state Coq machine use different
source calculi; neither theorem silently changes the other's scope.

See [experiments](../docs/EXPERIMENTS.md) and [verification scope](../docs/VERIFICATION.md).
