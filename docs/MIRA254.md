# The 254-state construction and combined experiments

Compared 15 October 2026 against
[busy-beaver commit 297ab8d](https://github.com/jeff87654/busy-beaver/tree/297ab8df7e5de329605c3875b4934643b371a5e3/ZF/m254).
**No machine smaller than 254 states was established in this experiment.**
The retained improvement is a register-program tree, not a new record TM.

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
executor: 8,387 ordinary returns, three counter overflows and one halt. This
does not mean we rebuilt its Coq proof. The Python model uses register-operation
contracts; the published Coq development proves those contracts and the complete
machine theorem. The comparison tool distinguishes these scopes.

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
They have no new Lean or Coq proof. They do not replace `ics-best.tm`, the Lean
headline, or the external 254-state record.

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

The next useful implementation is a compiler for their single-marker backend
that records where each contextual fold is valid. Reassociation would then
recheck or undo affected folds and score the actual final table. Multiple
source/tree candidates should survive until that score is available. The retained
202-node tree is a concrete test case: the backend must compile it below 254
with all instruction/boot checks passing, or account for the extra states needed
to restore correctness. A smaller register tree alone is not enough.
