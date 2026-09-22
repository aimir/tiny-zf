# Verification scope and intended contract

**Status: exact reproduction and computational checks, not a formal proof.**
There is no Lean development or verified ZF-independence theorem in this repo.
The 392-state table is a candidate based on the corrected upstream source.

## What `python3 tools/verify.py` checks

1. Every vendored file matches the SHA-256 digest recorded for the pinned commit.
2. Compiling the documented upstream order produces exactly the saved 393-state
   transition relation, with the same start state and blank-tape convention.
3. The two removed copies of B6b and B8b equal their retained copies as expanded
   structured instruction trees, independently of compiler node numbering.
4. The candidate order contains every distinct original axiom/inference clause,
   introduces no clause, and does not end with DET or GEN.
5. Recompiling that order gives the saved 392-state table transition for
   transition. Full local reduction and exact quotienting give the stated count.
6. Both literal tables survive the requested finite number of blank-tape steps.
   The report includes dispatch visits so the scope of the smoke test is visible.

With `--windows`, the verifier additionally repeats a sound finite-window
reachability overapproximation. It does not exclude any reference state/read
pair in the tested windows. The regression suite includes deliberate malformed
inputs and a rejected incorrect quotient, not just successful self-comparisons.

These checks establish reproducibility, clause coverage, table integrity and
some bounded behavior. Equality of clause sets alone is not an end-to-end
halting-equivalence proof: selector semantics, proof encoding, instruction
lowering, and tape layout are additional obligations.

## Literal machine semantics

A configuration is a control state, an integer head position, and a map from
integers to bits, initially zero everywhere. Each table row reads the head bit,
writes one bit, moves one cell left or right and selects the next state. A
missing transition halts. The designated label `halt` has no outgoing edges.
There are 392 operational states in the candidate, excluding that label.

The reduction tools use a complete table with a separate `HALT` target. Missing
source transitions become a write of the read bit, a move right, and `HALT`.
This adds a step at an undefined source transition. The intended correspondence
is existence of halting, not exact halting time or the terminal tape/head.

The strict table reader rejects nonblank initial-tape directives, unexpected
undefined targets, duplicate rows and nonbinary/non-L/R instructions. The
unmodified upstream parser is retained for reproduction, not relied on as a
strict external-file validator.

## Proposed end-to-end theorem, not yet approved or proved

For the literal checked-in candidate table `M`, a precisely defined source
proof predicate `SourceProof`, and the distinguished contradiction target `bad`:

```text
HaltsOnBlankTape(M) ↔ ∃ p : Nat, SourceProof(p, bad)
```

An additional theorem should connect existence of such a proof to existence of
a contradiction proof in a fixed conventional ZF presentation. This separates
implementation correctness from the mathematical relationship between theories.
It also makes it possible to audit an alternative ICS formulation without
silently replacing the meaning of the first theorem. These are mathematical
specifications, not Lean statements already accepted by a kernel.

The proof obligations are:

- **Logic and coding:** define well-formed formulas, inference rules, axioms,
  pairing, proof enumeration and the distinguished target; justify treatment of
  numeric codes that are not well-formed formulas.
- **Enumeration:** show soundness and completeness of the stack enumeration,
  including default clauses, inactive premise-loading clauses and out-of-range
  axiom selectors.
- **Deduplication / reordering:** translate finite derivations in both directions
  by renumbering clause selectors and their encodings. Repeated copies of a
  schema are unnecessary, but the renumbering argument must be formalized.
- **Compiler:** specify the structured instruction and relative jump semantics,
  verify DAG factoring/lowering, register primitives and bootstrap.
- **Tape invariant:** prove instruction-pointer/register-file separation and
  exclude unintended halts such as the missing `1.inc`/`1` entry.
- **Literal artifact:** tie the finite table and its state count to the compiled
  object. Any later reduction needs a checked simulation certificate.

Proving nonhalting outright is neither a regression test nor the intended
unconditional deliverable. Independence conclusions need their explicit
metatheoretic assumptions, as described in [the survey](SURVEY.md).
