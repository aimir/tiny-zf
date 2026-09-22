# ICS and compiler experiments — 23 September 2026

**Best candidate: 316 states, down from 392 (76 states / 19.4%).**
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
| Reversed payloads + fused tags | 339 | Change inner formula coding to share arithmetic with direct tag construction. |
| Shared stack pop | 333 | Leave the new theorem in its register and reuse the existing unpair routine. |
| Shared stack push | 326 | Move operands to the constructor pairing routine instead of keeping a second pairing implementation. |
| Shared parameter copies | 320 | Match the increment order used by detachment and safety comparisons. |
| Joint source and factoring search | **316** | Search safe inlining and grammar choices together with source layout and parameter naming. |

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

### Sharing the arithmetic routines

The current selector first unpairs the old theorem into scratch registers while
leaving the new candidate in `topwff`. A zero selector restores the old theorem;
a positive selector keeps the candidate. Both cases decrement the selector with
saturation, restore the stack tail, and clear scratch. The safety-phase restore
uses the same unpair routine. This removes a separate unpair specialization.

Stack push moves the old stack into scratch and calls the exact pairing routine
already used by formula constructors. It computes the same stack code while
removing another arithmetic specialization. Parameter copies then increment
scratch before the output register, matching the order already used by
comparison routines. Independent increments commute; the identical instruction
patterns can share nodes. These changes keep the axiom schemas, formula coding,
proof enumeration and register interface unchanged.

### Inlining and factoring

The compiler identifies straight-line sequences of closed blocks: each block's
relative jumps stay inside it apart from normal completion. It selectively
inlines these wrappers, then tries randomized common-subsequence extraction or
factoring by estimated savings. The final score is the actual machine count
after the complete reduction pipeline. A beam keeps multiple alternatives.

Inlining the main procedure itself made the search much slower without a better
result in the bounded probe. The focused search keeps that boundary and still
varies internal procedures. The chosen artifact is audited against the entire
unfactored source CFG: register operations and both decrement branches must
match, with unconditional jumps hidden. Normal completion and contradiction
halting are distinct exits. This finite check is stronger than sampling execution
traces, but it does not verify the checker, compiler backend, or theory in Lean.

## Searches and negative results

| Search | Configurations scored | Best final count |
| --- | ---: | ---: |
| ICS order, 40 generations, width 96 | 7,681 | 352 |
| Joint parameters/layout/lowering, 60 generations, width 128 | 15,361 | 347 |
| Add comparison-register reuse, 60 generations, width 128 | 15,361 | 343 |
| Add reversed payload encoding, 60 generations, width 128 | 15,361 | 339 |
| Exhaust per-operator lowering choices at the retained layout | 2,500 | 339 |
| **First ICS round** | **56,264** | **339** |

| Follow-up search | Configurations scored | Best final count |
| --- | ---: | ---: |
| Layout/parameters after arithmetic sharing | 23,041 | 320 |
| Inlining/factoring grid | 800 | 318 |
| Unrestricted grammar beam, 11 complete generations | 2,113 | 318 |
| Focused joint beam, 80 generations | 20,481 | 316 |
| Per-operator lowerings with sharing and factoring | 2,500 | 316 |
| Continued joint beam, 40 generations | 10,241 | 316 |
| **Follow-up total** | **59,176** | **316** |

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

The follow-up search budgets and initial/final configurations are recorded in
[the same manifest](../reference/ics-experiments.json): arithmetic sharing,
an 800-configuration factoring probe, an 11-generation unrestricted beam, an
80-generation focused beam, all 2,500 operator lowerings with sharing enabled,
and a further 40-generation beam from the new incumbent. Only complete recorded
generations count in these summaries; they are not counts of distinct machines.

Additional prototypes tested selective inference dispatch (332 states), all 16
formula evaluation-order masks (best 320 before factoring), and 15 adjacent-pair
factoring choices (best 325). These do not improve the shared 320-state source.
The inference and expression-order prototypes are retained for investigation;
they do not participate in the candidate and have no end-to-end equivalence
check. A globally dual pairing prototype was also larger and was discarded.

Local 3/5/7-step contractions and exact quotienting leave the candidate at 316.
Finite-window analysis still excludes no state/read pairs in the tested windows.
These failures are limits of the experiments, not lower bounds on equivalent
machines.

## Reproduce

```sh
python3 tools/verify_ics.py --windows
python3 -m unittest discover -s tests
python3 tools/experiment.py ics-order
python3 tools/experiment.py ics-joint
python3 tools/experiment.py ics-storage
python3 tools/experiment.py ics-encoding
python3 tools/experiment.py ics-operators
python3 tools/experiment.py ics-sharing
python3 tools/experiment.py ics-grammar-probe
python3 tools/experiment.py ics-grammar
python3 tools/experiment.py ics-shared-operators
python3 tools/experiment.py ics-grammar-followup
```

The recorded experiments supply their own initial configurations, so they can be
replayed independently. Add `--workers 1` to reduce process count or
`--generations 1` for a short search smoke test. The latter is not a full replay.
Results go under ignored `scratch/`. See [verification scope](VERIFICATION.md)
for exactly what the checks establish.

## Next useful experiments

The large gains in this round came from changing representations and sharing
whole arithmetic routines. Further work should target a cheaper instruction
backend and larger arithmetic or expression-level rewrites. The current
implementation already shares stack pairing and searches inlining with layout. Another long run of the same local
permutations is less promising than expanding the compiler's choices. Keep the
conservative baseline and the ICS dependency explicit while exploring these.
