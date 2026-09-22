# ICS and compiler experiments — 23 September 2026

**Best candidate: 339 states, down from 392 (53 states / 13.5%).**
This round is experimental. There is no Lean proof and no claim that the local
computational checks establish the theory's equivalence to ZF.

## What produced the reduction

| Stage | Best measured count | Change |
| --- | ---: | --- |
| Conservative starting point | 392 | Wade's distinct axiom clauses, reordered. |
| Initial ICS port | 358 | Corrected ICS formulation, parameterized POW/UNI, and a shared safety phase. |
| ICS clause-order beam | 352 | Reorder within the two safety phases. |
| Joint source/layout beam | 347 | Also permute schema parameters and explore constructor lowering. |
| Shared comparison scratch | 343 | Save the current theorem temporarily, reuse its register, remove the third scratch register, and search again. |
| Reversed payloads + fused tags | **339** | Change inner formula coding to share arithmetic with direct tag construction. |

These are measured configurations, not additive cost estimates. Different beam
runs can choose different layouts; in particular the storage search started from
a retained 348-state configuration whose storage rewrite initially gave 344.
[Exact initial configurations](../reference/ics-experiments.json) remove ambiguity.

### The ICS source

The formulas are taken from the
[corrected October 2025 source](https://github.com/CatsAreFluffy/metamath-turing-machines/commit/74a0e042f5f0ba433b3161b7c6b35ab319113844),
vended locally with its license. Its non-extensional set theory uses Powerset,
Union, and a combined Infinity–Collection–Separation scheme. The author sketches
why it has the same consistency strength as ZF. That mathematical dependency
remains to be established to our eventual verification standard.

We port the formula-construction sequences, not the entire NQL program. Wade's
proof enumeration and inference handling remain the starting point. Twelve
logical/inference clauses precede a phase containing POW, UNI, ICS, B6a1 and
B6a2. Before the latter phase, `param1` and `param2` are each incremented when
equal to `param3`. This implements the source's safety conditions. DET/GEN are
never the last clauses, avoiding Wade's documented inactive-inference hazard.

The checker extracts active constructor calls from the pinned NQL source and
compares all five protected formulas to the port. It also checks the bijective
parameter-renaming configurations. Those are transcription checks, not a proof
of logical soundness/completeness.

### Parameter naming as a compiler optimization

Every logical axiom schema can independently rename its three parameters by a
permutation. This changes neither its collection of instances nor its logical
formula template. It changes which push instructions occur next to one another,
which affects common-subsequence extraction. The protected phase uses a single
shared permutation; its safety guard is renamed consistently.

The beam retains 128 configurations rather than only the current champion. Each
new candidate is compiled and scored after the full local reduction pipeline;
no macro-count proxy decides the winner.

### Reusing the theorem register

The old equality checks used three scratch registers. In detachment, the theorem
register is already available during comparison. At the safety boundary, the
current theorem is pushed once onto the existing formula stack, allowing its
register to serve as comparison scratch, then restored before any protected
formula is constructed. The comparison code is shared between these uses.

All operations on the third scratch register disappear from the reachable
machine. There are ten active registers, although the inherited source builder
still declares the unused eleventh name. The bootstrap remains unchanged.
Local differential tests check restored theorem/stack contents and preserved
parameters, including equal and unequal comparison cases.

### Formula encoding and constructor fusion

Write `P(a,b) = a + (a+b)(a+b+1)/2`. A binary formula constructor formerly made
`P(P(left,right), tag)`. The current candidate makes
`P(P(right,left), tag)` instead. Negation still makes `P(formula,3)`. Tags are
unchanged: equality 0, membership 1, implication 2, negation 3, universal
quantification 4. Formula-stack pairing retains its original convention.

Reversing the inner pair is a bijective recoding of formula trees. It preserves
the distinguished codes 0 for `v₀ = v₀` and 1 for `v₀ ∈ v₀`. The bound variable
and body of universal quantification use the same reversed payload convention.

The compiler also pairs a payload directly with its tag instead of pushing the
tag onto the formula stack and immediately popping it. With the new inner order,
more of this arithmetic uses identical register patterns. This combination
worked even though direct tag fusion by itself did not improve the incumbent.
Tests check both encodings against the pairing formula and check untouched stack
tails and cleared scratch registers.

## Searches and negative results

| Search | Configurations scored | Best final count |
| --- | ---: | ---: |
| ICS order, 40 generations, width 96 | 7,681 | 352 |
| Joint parameters/layout/lowering, 60 generations, width 128 | 15,361 | 347 |
| Add comparison-register reuse, 60 generations, width 128 | 15,361 | 343 |
| Add reversed payload encoding, 60 generations, width 128 | 15,361 | 339 |
| Exhaust per-operator lowering choices at the retained layout | 2,500 | 339 |
| **Total** | **56,264** | **339** |

Counts include initial configurations and do not imply distinct transition
tables. Four worker processes were used. Search generations and complete beam
frontiers are disposable; Git contains only curated initial/final configurations
and aggregate results.

Additional bounded probes tested:

- Dispatching to one selected clause instead of constructing all clauses.
  The additional control structure outweighed the operations removed.
- Comparing/restoring parameters in place with a single scratch counter.
  The new instruction patterns shared less well with the existing comparisons.
- Conjoining the B6a clauses; conjoining POW/UNI; and using a common-witness
  POW/UNI alternative listed in the source. These did not improve their tested
  layout. None is used in the saved candidate.
- All 16 choices of inner operand order for the four binary constructors at a
  fixed lowering. Uniform reversal was best in that probe.
- All 2,500 per-operator scratch/fusion choices. The shared lowering remained best.

Local 3/5/7-step contractions and exact quotienting leave the final count at 339.
Seven finite-window reachability analyses retain all 678 state/read pairs; the
largest explores 980,791 abstract configurations. These failures are limits of
these experiments, not lower bounds on equivalent machines.

## Reproduce

```sh
python3 tools/verify_ics.py --windows
python3 -m unittest discover -s tests
python3 tools/experiment.py ics-order
python3 tools/experiment.py ics-joint
python3 tools/experiment.py ics-storage
python3 tools/experiment.py ics-encoding
python3 tools/experiment.py ics-operators
```

The recorded experiments supply their own initial configurations, so they can be
replayed independently. Add `--workers 1` to reduce process count or
`--generations 1` for a short search smoke test. The latter is not a full replay.
Results go under ignored `scratch/`. See [verification scope](VERIFICATION.md)
for exactly what the checks establish.

## Next useful experiments

The large gains in this round came from changing representations and sharing
whole arithmetic routines. Further work should target a cheaper instruction
backend, coordinated stack/pairing operations, and larger expression-level
rewrites searched jointly with layout. Another long run of the same local
permutations is less promising than expanding the compiler's choices. Keep the
conservative baseline and the ICS dependency explicit while exploring these.
