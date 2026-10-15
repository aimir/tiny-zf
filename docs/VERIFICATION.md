# Verification scope and intended contract

**The 252-state local-carry machine has a complete Coq proof of blank-tape
halting equivalence to conventional ZF/ZFC inconsistency.** Its literal table,
bootstrap, unbounded register operations, instruction execution, source program
and set-theory connection are checked together. See the
[Coq acceptance workflow](../formal/coq/README.md#verify-a-changed-machine) and
[verification record](../reference/mira252-local-coq.json).

**Status: the literal 308-state machine is formally verified against its numeric
source calculus in Lean.** The exact headline is:

```lean
theorem machine_correct : Machine308.Halts ↔ Source.Provable 1
```

The source calculus is defined independently of machine execution. The proof
covers the bootstrap, register and tape invariants, all optimized instruction
paths, graph equivalence, primitive arithmetic, decoder allocation, clause
execution, and exhaustive source enumeration. See the [entry theorem](../formal/TinyZF.lean)
and [verification guide](../formal/README.md). Its audited dependencies contain
only `propext`, `Classical.choice`, and `Quot.sound`.

The ICS/conventional-ZF interpretation and any ZF-independence conclusion remain
unproved. The conservative 392-state baseline and experimental native/dyadic
machines are outside this headline. The computational checks below remain
useful independent reproduction and regression checks; they are distinct from
the Lean proof.

## Conservative 392-state baseline: `python3 tools/verify.py`

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

## Experimental 308-state candidate: `python3 tools/verify_ics.py`

This command checks the candidate table hash, exact recompilation, the 65 + 243
state split and ten active registers. It compares five formula-construction
sequences with the pinned corrected ICS source, checks 90 schema-renaming
round trips, and runs 500 guard, 48 detachment, and 1,440 constructor cases in
an independent register-IR interpreter. The latter compare arithmetic results,
untouched stack tails and scratch cleanup; they do not formally verify the
interpreter or its correspondence with tape execution.

The current candidate rewrites UNI and ICS; POW, B6a1 and B6a2 choices happen to
reproduce their original syntax. An independent
reduced ordered Boolean decision diagram checker compares each selected formula
with the pinned original. Atomic formulas remain opaque; universal quantifiers
are indexed by their bound variable and the canonical Boolean form of their
body. Existential quantification expands as `not forall not`. Thus the check
permits classical Boolean equivalence and congruence under unchanged quantifier
scopes. It does not permit arbitrary changes to atoms, binders, or quantifier
order. Regression tests check all 268 individual rewrite choices and reject
changed connectives, membership/equality atoms, and binders. The twelve logical
axiom/inference clauses remain unchanged. Lean now proves semantic equivalence
of all five selected protected schemas in every first-order structure and
valuation. Translating these identities into derivations in the fixed calculus
remains an obligation; neither semantic equivalence nor the BDD check alone
establishes tape-machine halting equivalence.

The sharing pass adds 4,280 differential cases: 800 stack pushes, 2,400
selections, 540 parameter copies, 500 complete protected guards, and 40 selected
or inactive detachments. Each comparison checks every register, including scratch
cleanup and preservation of unrelated values. Together with the earlier checks,
there are 6,268 local arithmetic/differential cases.

The decoder audit checks the generated allocation with distinct symbolic tokens:
clears discard only old field values, moves target zero registers, each unpair
consumes the next proof tail into two zero registers, and all four fields and
scratch values satisfy the boundary contract. This assumes the existing arithmetic
primitive contracts; that Python resource check is accompanied by the unbounded
Lean theorem `Decoder.boundary_correct` for the same 16-operation arithmetic
plan. The separate Lean implementation proof now verifies those arithmetic contracts using primitive loops and literal tape transitions. A separate
integer model checks 1,000 decoder/enumerator boundaries, including arbitrary old
field values, theorem-stack contents and the empty-proof refill case. The remaining
inference body and halt test match the original body in a complete CFG comparison
(4,601 matched pairs).

The winning field order is `param1, param3, param2, axiomcode`. This changes the
numeric proof encoding. Nested Cantor pairing and a field permutation give a
bijection on instruction tuples; the positive-tail convention still makes every
finite tail traversal terminate. Lean now proves the two coding inverses, exhaustive
enumeration and the soundness/completeness equivalence for the numeric source
interpreter. The Lean headline now connects that interpreter to the optimized register/tape
program. Its connection to conventional ZF remains a mathematical obligation.
The literal-tape differential below compares the new tree with its **own decoder
source**, not with the old machine on the same proof numbers.

The pre-tree factoring audit compares the complete unfactored rewritten-source CFG with the
candidate's factored CFG. Each graph has 6,742 nodes; 4,659 reachable pairs of
operations/exits are matched after following unconditional jumps. Register names,
operations, and both decrement outcomes must agree. A normal return from `main`
and an explicit `halt` are different labels. An unconditional jump cycle is
also distinguished from termination. Regression tests reject alterations at
these boundaries. This checks all CFG branches, rather than a bounded execution
sample, but trusts the Python compiler/checker and does not prove tape-backend
correctness or the arithmetic sharing rewrites in Lean.

The final tree is a separate, hash-bound artifact. Its parser requires a finite
acyclic binary DAG with recognized register/jump primitives. The independent
CFG checker compares uninterrupted runs of increments by their per-register
multiplicities, then requires the same next decrement or exit and follows both
decrement successors. It matches **4,163 segment pairs** across the two 6,742-node
CFGs. This permits commuting increments while preserving all branch behavior,
including halt versus normal completion. Cycles containing only increments or
unconditional jumps are outside this checker and are rejected. No search history
or heuristic rewrite rule is trusted by the audit. This also covers fragments
transferred between sources by the combined search: its canonical signatures
select proposed replacements, while the complete result is independently checked
against the changed source. A regression case explicitly rejects retaining an
old whole-program tree after a formula mutation. Regression tests reject
changed increment counts/registers, movement across a decrement, swapped branch
outcomes and malformed tree references. They also audit every available single
rewrite at the incumbent and confirm that all 65 native framework states are
unchanged from the 313-state decoder source.

A literal differential check compares all ten registers at **512 decrement
boundaries**, including the 535 increments between them. The source takes
12,809,467 tape steps and the candidate 12,808,639 to reach those boundaries;
both have a minimum observed gap of seven cells. This is finite evidence that
the new dispatch paths implement the intended operations, not an unbounded
backend proof. Use `--tree-boundaries 0` to omit this longer check.

A separate literal one-million-step tape simulation visits the main dispatch
1,010 times and enters register primitives 993 times. The minimum observed
zero gap before the next register-file 1 is seven cells. This is a diagnostic
for that finite execution, not a proof of perpetual separation. `--windows`
adds seven finite-window reachability experiments. They have not been rerun for
308; the earlier 310-state table retained all 620 state/read pairs in those windows.

Relative to the conservative baseline, the source omits Extensionality and uses
the published ICS scheme. The sharing/factoring passes keep their input schemas
and formula encoding unchanged; the separate formula pass supplies the identities
described above. The claimed equiconsistency of ICS with ZF remains an explicit
dependency.
The Lean implementation theorem includes the actual reversed-payload coding. Matching the
published constructor sequences and passing finite tests do not discharge
these obligations. [Experiments](EXPERIMENTS.md) describes both transformations.

## Native tape experiments

These experiments do not change the current 308-state table. Adjacent-transfer
artifacts expand their new primitive into the original register loop for complete
source and tree CFG checks. Separate randomized literal-tape fixtures check both
kernels; an atomic-IR oracle checks all register values and operation dispatch
across 1,024 operations from blank tape. Transfer artifacts also run the ordinary
ICS verifier. These finite checks assume the unary-layout contract and do not
prove it for every future execution.

The exposed-address experiment requires `verify_native.py`. Its checker resolves
the selection counter into logical register operations, rejects invalid selection
flow, compares the entire resolved CFG, rebuilds the table exactly and compares
1,024 literal operations with the independent IR model. It currently supports
ordinary increments/decrements. See [native contracts and recipes](NATIVE.md).

The [fused-unpair experiment](UNPAIR.md) adds a Cantor diagonal-step contract and
an exit that restores the tail into the consumed input. Numerical checks include
nonzero initial outputs, comparison with the integer Cantor inverse, 1,000 decoder
boundaries and literal `cstep` execution. Its source audit expands fused calls
into the old contracts and checks the complete resulting CFG. Increment-first
variants also require a direct expanded-source CFG match; decrement-first variants
can change the operation trace. The reports distinguish contract-based
matches from direct matches. Factoring and tree checks use the actual new program.
None of these finite checks proves the unbounded tape invariant.

## Literal machine semantics

The separate [dyadic pairing experiment](PAIRING.md) has its own builder and
`verify_pairing.py` checker. It checks numerical arithmetic contracts, consistent
constructor/stack/decoder interfaces and each finalist's CFG and finite tape
behavior against its recoded source. It does not compare that arithmetic trace
with the incumbent's Cantor computation. The current candidate retains Cantor arithmetic. Its decoder allocation and field
order are described in [the decoder report](DECODER.md).

A configuration is a control state, an integer head position, and a map from
integers to bits, initially zero everywhere. Each table row reads the head bit,
writes one bit, moves one cell left or right and selects the next state. A
missing transition halts. The designated label `halt` has no outgoing edges.
There are 308 operational states in the ICS candidate and 392 in the
conservative baseline, excluding that label.

The reduction tools use a complete table with a separate `HALT` target. Missing
source transitions become a write of the read bit, a move right, and `HALT`.
This adds a step at an undefined source transition. The intended correspondence
is existence of halting, not exact halting time or the terminal tape/head.

The strict table reader rejects nonblank initial-tape directives, unexpected
undefined targets, duplicate rows and nonbinary/non-L/R instructions. The
unmodified upstream parser is retained for reproduction, not relied on as a
strict external-file validator.

## Proved implementation contract and remaining theory bridge

[TinyZF.lean](../formal/TinyZF.lean) proves the fixed target
`Machine308.Halts ↔ Source.Provable 1`. Its statement uses the literal candidate
and the independently defined numeric calculus with the actual guarded and
rewritten schemas. All implementation layers are discharged, including inactive
premise loading, selector saturation, arbitrary register values, and unbounded
execution. No compiler-correctness assumption is present.

An additional theorem would connect a derivation of numeric code one with a
contradiction proof in a fixed conventional ZF presentation. That requires
interpreting the exact source schemas and inference rules, including the ICS
scheme and selected rewrites. It is deliberately separate from implementation
correctness. A ZF-independence conclusion also requires explicit metatheoretic
assumptions, as described in [the survey](SURVEY.md).

The finite Python graph checks above retain a distinguished `return` node,
whereas the Lean whole-program graph redirects normal iteration returns to the
entry. Thus the Lean certificates have 6,741 instructions and 4,162 common
blocks, while the finite fragment reports count 6,742 nodes and 4,163 pairs.
Those are different interfaces to the same iteration, not missing Lean cases.

Any future machine change requires its own checked artifact and correspondence;
the current theorem is specifically bound to the saved 308-state table.
