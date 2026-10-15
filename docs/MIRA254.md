# The 254-state construction and combined experiments

Compared 15 October 2026 against
[busy-beaver commit 297ab8d](https://github.com/jeff87654/busy-beaver/tree/297ab8df7e5de329605c3875b4934643b371a5e3/ZF/m254).
**No machine smaller than 254 states was established in this experiment.**
The retained program-tree changes now include a native 254-state variant with
a complete Coq proof. This matches the reference size, rather than improving it.

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
a smaller register tree alone is not enough. Further search continues toward
a machine below 254, with full formal acceptance required for each result.
