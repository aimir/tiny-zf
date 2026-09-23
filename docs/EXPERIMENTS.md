# ICS and compiler experiments — 23 September 2026

**Best candidate: 308 states, down from 392 (84 states / 21.4%).**
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
| Joint source and factoring search | 316 | Search safe inlining and grammar choices together with source layout and parameter naming. |
| Protected-formula rewrites and joint search | 315 | Preserve the logical/inference clauses; search equivalent protected formulas, source layout and factoring seeds. |
| Dispatcher-tree reassociation and commuting increments | **310** | Share more binary instruction nodes while preserving the register computation. |
| Combined source/tree search and checked fragment transfer | 310 | Three bounded runs found alternative 310-state constructions, but no smaller machine. |
| Joint decoder allocation and instruction-tree search | **308** | Decode fields in a different order, delay destination clears, and search 16 final trees. |

These are measured configurations, not additive cost estimates. Different beam
runs can choose different layouts; in particular the storage search started from
a retained 348-state configuration whose storage rewrite initially gave 344.
[Exact initial configurations](../reference/ics-experiments.json) remove ambiguity.

The later [dyadic pairing/unpairing experiment](PAIRING.md) tested two coding
orientations, three pair kernels, two inverse kernels, specialized tags and
multiple source/tree finalists. Across 9,909 source evaluations and 245,760 tree
mutation attempts, ordinary dyadic pairing reached 321 states and reversed
dyadic pairing reached 323. Both winners passed their dedicated computational
checks; neither replaced the 310-state Cantor machine.

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

### Equivalent protected formulas

The new beam first converts each protected schema to negation normal form,
chooses the operand order of each Boolean conjunction/disjunction, and lowers it
back to implication, negation and universal quantification. Existentials use
`not forall not`; quantifier scopes are preserved. The source macros for
conjunction and existential quantification are recovered where they match.
These syntactic changes alter repeated compiler instruction patterns.

There are 4 POW, 4 UNI, 256 ICS, 2 B6a1 and 2 B6a2 rewrite choices, plus the
original syntax for each. The beam varies these together with source order,
parameter naming, arithmetic lowering and the factoring seed. Its width is 128,
with 256 new configurations per generation, four workers and 80 generations.
Every score uses full table reduction. The best result appeared at generation
47: **65 framework + 250 DAG = 315 states**. It changes UNI and ICS syntax;
its POW/B6a1 choices reproduce their originals and B6a2 stays original.

An independent Boolean decision diagram checker checks the selected identities,
treating quantifiers as congruent operators on canonically equal bodies.
It does not use the rewrite generator's NNF algorithm. All 268 generated
individual choices pass, and deliberate invalid changes fail. The logical
axiom basis and inference rules are fixed throughout. This makes the intended
equivalence argument much narrower than replacing that logical basis, but the
identities and their use in the proof enumeration still need formal derivations.

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

| Further search | Configurations scored | Best final count |
| --- | ---: | ---: |
| Protected formulas, layout and factoring, 80 generations | 20,481 | **315** |

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

Further bounded structural probes from the 316-state layout tried:

- Reassociating closed binary instruction blocks, with an exact CFG audit: 316.
- Linear `5 * payload + tag` coding: best 324 in the tested variants.
- Keeping a separate theorem accumulator: 325 with factoring.
- Stopping clause construction once the selector is exhausted: 335 with factoring.
- Simpler premise-selection control flow: best 322 across 16 tested variants.
- Permuting the three non-atomic tags at the retained 316/315 layouts: no improvement.

These discarded prototypes are not part of the candidate; their measured sizes
do not establish semantic correctness or rule out better implementations of the
same ideas. Raw prototypes and search traces are not repository artifacts.

Local 3/5/7-step contractions and exact quotienting leave the current candidate at 308.
Finite-window analysis excluded no state/read pairs for the earlier 310-state table;
those windows have not been rerun for 308.
These failures are limits of the experiments, not lower bounds on equivalent
machines.

## Dispatcher/backend round

This earlier 310-state result kept the 65-state native framework unchanged and reduced
the decision DAG from 250 to **245 states**. The compiler can now consume an
explicit final instruction tree, checked independently against the source.

The first tree search allowed more reassociations than the earlier closed-block
rule. In `((a,b),c) ↔ (a,(b,c))`, the middle block need not itself be closed;
constraints on escaping jumps determine when a rotation preserves control flow.
This gave **312 states** after 400 generations of 256 mutation attempts, retaining
64 candidates. The best first appeared at generation 101.

The next search adjusted relative continue jumps when moving a block and allowed
adjacent increment-only sequences to commute. It kept candidates at three nearby
cost levels, with up to 80 retained trees. After 600 generations of 256 attempts,
the best was **310**, first found at generation 189. These are mutation-attempt
counts, including duplicates; they are not counts of distinct compiled machines.
The source formulas, arithmetic lowering and ten physical registers are unchanged.

The reusable search now screens by exact raw size, fully reduces a configurable
number of leaders each generation, and fully reduces the final retained frontier.
Every saved improvement passes the independent increment-segment CFG audit.
A 20-generation run using this fuller scoring held at 310. The tree arena is
compacted each generation, avoiding unbounded accumulation of old candidates.

Other bounded probes did not improve that result:

- Exposing register-selection chains to grammar compression and varying register
  placement scored 6,401 configurations, with a best of 319.
- Broader relative-jump adjustments and changes to individual uses of shared
  nodes held at 310 in the tested runs.
- A simple three-valued register analysis retained every decrement outcome and
  every dispatcher read edge.
- A global segmentation model had 847,405 edge variables and returned a 310-state
  candidate in a 180-second run.
- A smaller binary-grammar model had 4,173 candidate words and 48,297 productions.
  In 180 seconds it found 310, with a model bound of 288. A further 240-second run
  targeting at most 309 with a zero-run limit of seven returned **UNKNOWN**: no
  feasible candidate and no impossibility result.

These solver bounds concern the finite dictionary/grammar model, not equivalent
Turing machines. OR-Tools 9.15.6755 was used with four workers and a 4 GiB solver
memory setting. The binary model is retained in `solve_tree.py`; its candidates
are rebuilt and independently audited before saving. Raw solver logs and model
files are excluded. [The backend manifest](../reference/backend-experiments.json)
records source parameters, recipes and aggregate results.

## Combined source and instruction-tree search

`search_combined.py` closes a gap in the earlier experiments: source searches
ranked compiler output, while tree search optimized one frozen source. The new
outer beam retains several sources, each with several saved instruction trees.
It mutates the source, screens raw compiler sizes, optimizes the shortlisted
trees, and fully reduces every final inner frontier before selecting sources for
the next generation. A smaller set receives deeper searches. The source choices
include protected-formula syntax, clause order, parameter naming, constructor
lowering, payload direction, inlining and factoring.

Closed register-code fragments can also transfer from a champion or mutation
parent to a changed source. Their normalized CFG signatures must agree; the
complete retained program is then independently audited against its own source.
A regression test rejects a stale whole-program tree after a formula change.
The raw-size screen remains heuristic, so a separate option reserves shortlist
slots outside its cutoff. These slots give other lowering/factoring families a
chance to improve after tree optimization.

The first four-generation pass screened **769 source configurations**, attempted
**573,696 tree mutations**, and fully reduced **5,188 tree candidates**, retaining
up to 16 sources with four trees each. It held at **310**, but established useful
ranking reversals: a 316-state source reached 310 and a 319-state source reached
311, while some 315-state sources finished at 312–313. Counts include repeated
initial configurations and tree attempts; they are not distinct-machine counts.

Two further runs resumed the complete first-pass population. One used twelve
outer generations, up to 24 sources, and deeper searches of six finalists per
generation. The other screened 2,048 new sources per generation for four
generations, with shorter tree searches. Both transferred fragments from mutation
parents and reserved four shortlist slots outside the normal raw-size cutoff.
Both finished at **310** and left that round’s candidate unchanged.

| Recorded run | Source evaluations | Tree mutation attempts | Full tree reductions | Best |
| --- | ---: | ---: | ---: | ---: |
| Initial combined beam, 4 generations | 769 | 573,696 | 5,188 | 310 |
| Parent transfer, 12 generations | 3,088 | 878,592 | 19,154 | 310 |
| Wider source screening, 4 generations | 8,208 | 129,024 | 4,206 | 310 |
| **Total** | **12,065** | **1,581,312** | **28,548** | **310** |

The deeper run used four workers with a cooperative 512 MiB budget each; measured
peak worker memory was 229 MiB. The other runs used two workers. Both final search
artifacts passed the complete artifact verifier, including local arithmetic and
formula checks, CFG audits, one million literal tape steps, and comparison of all
ten registers at 512 decrement boundaries. These are computational checks, not
formal proofs. Their small aggregate check reports are included in the manifest.

The exact starting tree and source are saved with
[the combined experiment recipes](../reference/combined-experiments.json).
Frontiers and console logs remain in scratch storage. The search can reload and
audit a whole frontier, including the incumbent's alternative trees. A small
restart experiment produced identical machines and retained source/tree frontiers
with two and four workers. The default is two workers; the memory setting is a
cooperative resident-memory budget checked between tree generations, not a hard
operating-system limit.

## Decoder and register allocation

The [decoder campaign](DECODER.md) tested direct writes into destination fields,
rotating proof tails, deferred parallel moves, eager or delayed clears, and field
permutations together with the existing source and factoring choices. Two beams
evaluated **8,102 source configurations** and optimized **32 finalists**, reaching
**308 states** with ten registers and **313** with a packed nine-register design.

The accepted result preserves the Cantor arithmetic kernels and inference body.
It decodes `param1, param3, param2, axiomcode`, clearing each destination just
before transferring its value. The instruction tree has 243 states and the
native framework still has 65. The raw and fully reduced tables both have 308
states. Proof numbers now encode fields in a different order; no claim is made
that the same numeric code has the same trace as the 310-state machine.

The new decoder has a symbolic live-value audit, numerical register-boundary
checks and a complete CFG comparison of the unchanged inference body. The final
table passes the existing rebuild, arithmetic, formula, CFG and literal-tape
checks. See the [recorded recipes](../reference/decoder-experiments.json).

## Native tape operations and placement

The [native-tape campaign](NATIVE.md) combines adjacent destructive addition,
physical register placement and decoder allocation with width-128 source beams
and 32 tree finalists per campaign. A six-state left-transfer kernel and exact
selector-layout optimization bring optimized native-transfer trees to 311 states.
Exposing register selection to the instruction tree finishes at 309. Directly
shortening the existing dispatcher fails its control-context checks. The 308-state
incumbent is unchanged; exact recipes and aggregate checks are in the
[native manifest](../reference/native-experiments.json).

## Fused unpairing and tail restoration

The [fused-unpair experiment](UNPAIR.md) varies four arithmetic loop arrangements
and three independent restoration sites. A seven-state native kernel implements
the common Cantor diagonal step, with two selector states. A width-128 beam
combines these with allocation and the existing source choices, then optimizes
32 trees. A further whole-tree search reuses the 308-state incumbent only after
a complete CFG match. The [manifest](../reference/unpair-experiments.json) records
all counts and results: 3,998 source evaluations, 404,480 tree mutations, and
16 native-tree expansions. Source fusion and expansion both reached 308; the
native kernel reached 313. The incumbent remains unchanged. Arithmetic contract checks remain separate from compiler
and tape checks; there is no new Lean theorem.

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
python3 tools/experiment.py ics-rewrites
python3 tools/experiment.py backend-tree-commute
python3 tools/experiment.py combined-source-tree
python3 tools/experiment.py combined-parent-transfer
python3 tools/experiment.py combined-wide-screen
python3 tools/experiment.py decoder-allocation
python3 tools/experiment.py decoder-packed-counter
python3 tools/experiment.py native-placement
python3 tools/experiment.py native-addresses
python3 tools/experiment.py unpair-fusion
python3 tools/experiment.py unpair-whole-tree
python3 tools/experiment.py unpair-expanded
```

The recorded experiments supply their own initial configurations, so they can be
replayed independently. Add `--workers 1` to reduce process count or
`--generations 1` for a short search smoke test. The latter is not a full replay.
Results go under ignored `scratch/`. See [verification scope](VERIFICATION.md)
for exactly what the checks establish. The backend replay regenerates its
312-state starting tree before running the second stage; `--generations 1` also
shortens that prerequisite. The two resumed combined runs likewise replay their
first-pass population before continuing; a generation override shortens both stages.

## Next useful experiments

Getting below 300 requires nine more states. Joint decoder allocation recovered
two states after tree optimization; packing the counter saved a physical register
but added more instruction machinery than it removed. Adjacent native transfers currently add more kernel/selection states than they
remove from the tree. Larger fused arithmetic routines, a redesigned dispatcher
or a different register representation remain possible directions.
These bounded results are not lower bounds on equivalent machines.
