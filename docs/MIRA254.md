# From Mira's 254-state construction to a verified 250-state machine

Pinned to [busy-beaver commit 297ab8d](https://github.com/jeff87654/busy-beaver/tree/297ab8df7e5de329605c3875b4934643b371a5e3/ZF/m254).
**The protected-startup machine has 250 states and a complete Coq proof of
blank-tape halting equivalence to ZF/ZFC inconsistency.** Its
[table](../candidates/mira250-protected.tm),
[unchanged decoder tree](../candidates/mira250-protected.tree.json), and
[proof record](../reference/mira250-protected-coq.json) are included.

## The 250-state reduction

Register placement and global constraint solving permit the return state 5 to
share state 48. The physical permutation of the original nine register slots is
`[0,3,1,4,2,5,6,8,7]`. Eight transition changes choose compatible decoder and
return paths; [`mira_forward.py --mode protected`](../tools/mira_forward.py)
contains the complete deterministic recipe, starting from the pinned table.
The underlying 203-node program tree and arithmetic contracts are unchanged.

The shared startup reaches a nonempty program counter after **2,187,238 steps**,
with a 57-cell counter area, physical active registers `[3,1,6,1,0,0,0,0,0]`,
and 619 inactive registers. The inactive tail contains a one, and is included
exactly in both the independent simulation and Coq bootstrap theorem.
Initialization enters partway through AX construction rather than at a source
iteration boundary.

The [complete source bridge](../formal/coq/protected_startup.v) executes two
candidate RM steps, transports through the checked bisimulation's entry 148,
computes 347 small source steps, and proves the remaining structured AX suffix
with unbounded arithmetic lemmas. Three control steps then return to enumeration
at candidate zero with zero current and cached formulas, but an arbitrary stack.
No giant formula code needs to be computed.

The [stack-protection theorem](../formal/coq/stack_protection.v) supplies the
necessary source contract. For every NIP, replacing selector 2 by selector 1
produces a distinct earlier DROP in the enumerated programs. Consequently each
prefix has enough newly pushed derivable formulas that NIP never reads the
arbitrary original stack. Completeness follows from the general initialization
proof. This discharges the initialization obligation without assuming that the
stack contains only theorems.

The final build checks all 6,460 instruction sites, complete tape simulation,
source equivalence and all three ZF/ZFC/SIR theorems. Every final assumption audit
reports `Closed under the global context`. The bounded search proposed the
sharing; it is not part of the trusted proof or a lower bound on smaller machines.
[Reproduction instructions](../formal/coq/README.md#verify-a-changed-machine).

## The 251-state reduction

Starting from the 252-state machine below, change `0:1` to `0 L 4`, `5:1`
to `0 L 5`, and `109:0` to `0 R 85`, then remove state 8. Marking register
zero now returns through state 6, and increment takes a short detour through
the existing decrement state at the end of the file. These changes allow
initialization to share the remaining interpreter states.

Blank-tape execution reaches its exact initial configuration in **182,904
steps**: a 40-cell program-counter gap, `nextproof = 3`, `param1 = 1`, the
other seven active registers zero, and 95 extra zero registers. This is the
source enumerator's state after its first three commands. A finite Coq proof
connects it to the original start; the complete unbounded tape-to-ZF/ZFC chain
is then rebuilt. The program's 203-node tree is unchanged.

The [increment proof](../formal/coq/startup_increment.v) establishes the new
return path for arbitrary register suffixes. The acceptance driver also checks
the changed mark return and the exact bootstrap. This is a complete machine
proof, not acceptance based on a plausible initial tape shape.
[`mira_forward.py --mode startup`](../tools/mira_forward.py) reproduces the table.

## The 252-state decrement reduction

The decrement routine uses a two-state positive-decrement loop. State
112 fills the gap, and state 85 erases the next one. When that next cell is
followed by another one, a three-step local swap moves the gap one cell farther
right. The loop reaches each separator with exactly the register encoding
required by the existing suffix-induction proof. A separate run-scanning state
is unnecessary.

Starting from the 253-state stream below, change `112:0` to `1 R 85`, `112:1`
to `1 L 112`, `85:0` to `0 L 63`, and `85:1` to `0 R 112`, then remove state 97.
The [local carry lemma](../formal/coq/local_decrement.v) proves this behavior
for arbitrary run lengths. The complete Coq build checks all dependent proofs
and all three ZF/ZFC/SIR endpoints. Exact blank-tape initialization takes
**267,192 steps**. The program tree and source interpreter are unchanged.

A bounded constraint search proposed the small transducer; independent kernel,
instruction and bootstrap checks screened it before the unbounded Coq proof.
The finite synthesis bounds are not part of the final theorem.
[`mira_forward.py --mode local`](../tools/mira_forward.py) reproduces the table.

## The 253-state block-streaming reduction

The original positive-decrement routine scans to the end of the register file
and shifts the suffix backward. The new routine moves the deleted-cell gap
forward through the suffix. It restores the gap to one, scans the next run of
ones, and erases its last one. At the end it appends the same zero register as
the original operation. This permits the gap state and one continuation state
to share a single state, saving one working state.

The exact change from the pinned table redirects `75:1` to `1 L 112`, changes
`112:0` to `1 R 97`, `112:1` to `0 R 112`, `97:0` to `0 L 63`, and `85:0` to
`0 L 112`, then removes state 131 and redirects its incoming edges to 112.
[`mira_forward.py --mode forward`](../tools/mira_forward.py) applies these changes and renumbers
the table while preserving the proof's named operation states.

The source program and its 203-node decoder tree are unchanged. The complete
blank-tape bootstrap takes 284,880 steps. The
[new kernel proof](../formal/coq/forward_decrement.v) covers arbitrary register
values and suffixes, including the uniform positive-decrement return in state
48. Coq then checks the interpreter and the entire source-to-ZF/ZFC chain.
All three headline theorems are closed under the global context.
[Artifact and proof reproduction](../formal/coq/README.md#verify-a-changed-machine).

## Attribution and verification

Mira-Cult designed the machine. Jeffrey Ketchersid's repository supplies its
literal table and an end-to-end Coq proof connecting blank-tape halting to
inconsistency of the library's conventional ZF and ZFC. Its README credits the
source program, compact calculus, single-marker interpreter and state merges to
Mira-Cult. This is a stronger mathematical endpoint than our Lean theorem,
whose right-hand side is the numeric ICS source calculus.

The linked Mira-Cult repository returned 404 during this comparison. Ketchersid's
copy does not redistribute `source.py` or `paths.json`, but its checked Coq
definitions contain both program trees. We recover those definitions directly,
with input hashes pinned in [the comparison tool](../tools/compare_mira254.py).
The table's SHA-256 is
`d655ce2cf8cccebd21caa21a49f0f9f010960a44b95c17aae6cc425c518954eb`.

We reproduced all 8,391 instruction cases in the upstream Python symbolic
executor: 8,387 ordinary returns, three counter overflows and one halt. The
Python check uses register-operation contracts. We also completed a separate
clean build of the entire upstream Coq development: all three headline theorems
report `Closed under the global context`. See the [Coq verification guide](../formal/coq/README.md)
and [compact build record](../reference/mira254-coq-verification.json). The Coq
proof establishes those register contracts and the complete machine theorem.

## Where the reduction comes from

Recompilation with our pinned, unmodified Wade backend gives:

| Construction | Shared program nodes | TM states |
| --- | ---: | ---: |
| Our current ICS machine | 243 | 308 |
| Their source DAG on Wade's backend | 219 | 281 |
| Their optimized tree on Wade's backend | 203 | 265 |
| Their final single-marker implementation | Shared with interpreter states | 254 |

This gives a reproducible comparison of **27 + 16 + 11 = 54 states**. These
are differences between complete configurations, not independent savings that
can necessarily be added in another order.

The important changes are:

1. **Logical basis and set theory.** Łukasiewicz's single implicational axiom
   replaces several propositional rows. A powerset-container principle and
   global-image collection, together with irreflexivity, replace the older
   set-theoretic presentation. Coq proves the required consistency equivalences;
   these are not merely reorderings of our schemas.
2. **Four formula constructors.** Negation is implication into the false code.
   Formula codes are `4 * P(x,y) + tag`, with dual Cantor pairing and tags for
   implication, membership, universal quantification and equality. Our failed
   five-tag linear-coding experiment did not test this combined change of logic
   and coding. Four tags make the multiplier a power of two and remove a primitive
   constructor.
3. **Proof enumerator.** A cached theorem, stack commands and an AX command
   producing a group of theorem instances replace the old selection mechanism.
   Nine registers reuse the selector as the third parameter. Several helpers
   consume inputs or accumulate outputs instead of restoring or clearing them.
4. **Tape interpreter.** A single marker separates the program counter from the
   left blank region. Three decoder passes prepare the tape, select a register,
   and execute the operation. Decoder nodes, control paths and arithmetic leaves
   share states using nearby tape bits as context. Running time is traded for
   fewer states.
5. **Tree and table optimization.** Reassociation, commuting increments and
   contextual sharing contribute too. These overlap our methods; their savings
   cannot simply be added a second time.

See the upstream [logic design](https://github.com/jeff87654/busy-beaver/blob/297ab8df7e5de329605c3875b4934643b371a5e3/ZF/m254/design/logic.md)
and [tape design](https://github.com/jeff87654/busy-beaver/blob/297ab8df7e5de329605c3875b4934643b371a5e3/ZF/m254/design/tm.md).
Some design notes retain older status prose; the final README and theorem files
state the completed proof's scope.

## Combined experiment

All-tape contractions and exact quotienting leave their table at 254 states.
Reachability windows through 17 cells exclude no state/read pair. Further bounded
contextual contraction, trace-joining and bootstrap-substitution probes found
no smaller valid machine. These negative results are not lower bounds.

The recovered optimized program seeds a beam with width 64, 256 mutation attempts
per generation, 120 generations and seed 25420261015. The run makes 30,720 mutation
attempts and fully reduces 424 leading/retained candidates on Wade's backend.
It improves the program tree from **203 to 202 shared nodes**, producing
**264 instead of 265 states on Wade's backend**. The complete CFG comparison
checks 3,863 related increment segments and their decrement/exit continuations.

The [retained tree](../reference/mira254-tree202.json) and
[measured results](../reference/mira254-comparison.json) are small text artifacts.
That older saved layout has no new Lean or Coq proof. It is distinct from the
202-node tree of the native variant below. Neither replaces `ics-best.tm` or
changes the scope of the 308-state Lean headline.

### Rejected 253-state transplant

One rotation changes `(A,(B,C))` to `((A,B),C)` and reuses a shared `(A,B)` block.
Redirecting state 178's two edges to states 16 and 206 makes state 208 unreachable:
the graph has 253 states. The register-program change passes the CFG check.

But the final tape states have additional uses tied to surrounding PC bits.
The upstream symbolic executor rejects the modified table on instruction cases.
This is a correctness failure, not a missing proof certificate. The tool
reproduces this rejection without saving the invalid table as a candidate.
It checks outcome counters explicitly: the upstream script can report failures
while returning exit status zero.

An independent literal simulation also supplies a concrete counterexample:
instruction site 894 decrements `topwff`, with all twenty physical registers
initially zero. After 588 tape steps the modified interpreter returns with the
wrong program counter. This disproves the instruction contract; it does not by
itself settle the modified table's halting behavior from blank tape.

### Repaired native variant and its proof

The failed transplant also redirects a backtracking path through states 218
and 154. Its use of state 178 depends on the old layout. A separate copy of
state 154 preserves that path: its zero edge uses state 206, whose zero edge
supplies the behavior formerly obtained from 178. Ordinary dispatch can then
use the rotated tree. Removing 208 and adding this context-specific state
leaves **254 states**.

The [native compiler](../tools/mira_native.py) reproduces this repair. It writes
the table and its exact matching tree together, with hashes. The public
[table](../candidates/mira254-rotation.tm) is the densely renumbered table
checked by Coq; its [tree](../candidates/mira254-rotation.tree.json) has 202
shared nodes. All 8,391 symbolic cases pass. Blank-tape execution reaches the
full prescribed initial tape after 264,982 steps.

The [candidate proof driver](../formal/coq/candidate.py) regenerates the decoder
and a 3,009-entry bisimulation certificate against the unchanged 219-node source.
Coq checks both directions of that certificate and the entire tape-to-ZF/ZFC
proof. All three headline theorems are closed; the
[record](../reference/mira254-rotation-coq.json) identifies the exact table and
tree. See [how to rebuild](../formal/coq/README.md#verify-a-changed-machine).

The candidate proof also establishes the stronger 62-cell minimum PC-capacity
invariant supplied by the bootstrap. The upstream instruction checker used
40 cells. The larger bound allows searches to consider layouts and transition
rewrites needing more padding, while preserving the same blank-tape theorem.
The accelerated symbolic checker is tested against the pinned Python model;
its search results still require the complete Coq acceptance run.

The proof check also caught an actual integration error during development:
the older saved 202-node tree was initially paired with this new table. That
combination fails 136 symbolic cases and Coq's instruction-site theorem. The
successful record is for the exact matching tree linked above.

## Reproduce

Obtain the pinned upstream checkout, then run from this repository:

```sh
git clone https://github.com/jeff87654/busy-beaver.git /tmp/busy-beaver-m254
git -C /tmp/busy-beaver-m254 checkout 297ab8df7e5de329605c3875b4934643b371a5e3
python3 tools/compare_mira254.py --upstream /tmp/busy-beaver-m254 \
  --verify-tree reference/mira254-tree202.json --symbolic-check --probe-graft
```

Repeat the beam:

```sh
python3 tools/compare_mira254.py --upstream /tmp/busy-beaver-m254 \
  --generations 120 --width 64 --batch 256 --seed 25420261015 \
  --output scratch/mira254-beam.json
```

The input files are hash checked. The beam checks each improvement and its final
result against the original register CFG, compacts its arena each generation,
and fully scores the final frontier. Its score is explicitly labeled as the
**Wade backend** count. Logs, temporary tables and frontiers are not committed.

## What our search missed and the next useful step

Our search explored many layouts within a substantially fixed calculus and
interpreter. We changed ICS formulas, arithmetic and allocation, but did not
jointly redesign the logical basis, proof language, encoding and interpreter.
The failed five-tag and native-operation experiments did not establish that this
architecture was exhausted. This was a limitation of the search space, not
evidence that 308 was near an optimum.

The native compiler and candidate proof driver now support that next step.
Reassociation must recheck or undo contextual sharing and score the actual
final table. Multiple checked layouts are retained for further merging.
The repaired variant accounts for the extra state needed by one such rewrite;
a smaller register tree alone is not enough. Further search targets
250 states or fewer, with full formal acceptance required for each result.
