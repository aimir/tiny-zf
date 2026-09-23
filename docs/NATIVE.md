# Native tape operations and physical register placement

**The incumbent remains 308 states.** The best adjacent-transfer experiment has
311 states; exposing register-selection instructions finishes at 309. These are
bounded search results, not lower bounds. None is formally verified.

| Construction | Framework | Instruction DAG | Total |
| --- | ---: | ---: | ---: |
| Incumbent | 65 | 243 | **308** |
| Best adjacent-transfer tree | 75 | 236 | 311 |
| Exposed register selection | 46 | 263 | 309 |

The best transfer saves seven instruction nodes but adds ten kernel/selector
states. Across the source and tree campaigns we evaluated **8,532 source
configurations** and **763,520 tree mutation attempts**, including the deeper
follow-up. Counts include repeats and do not imply distinct machines.

## Transfer contract

The ordinary structured program expresses destructive addition as
`while source.decnz: destination.inc`. The new compiler option recognizes this
exact loop when the two physical registers are adjacent. Its contract is

```text
(source, destination) = (a, b)  →  (0, a + b)
```

Every other register is preserved. Both zero and nonzero inputs are allowed;
the destination need not be zero. The routine moves unary register separators
instead of dispatching one decrement and increment for every unit transferred.
This is a state-count experiment; runtime was not the search objective.

Registers are unary runs of `value + 1` ones. Declaration order runs from right
to left on the tape, so adjacent declaration indices have the opposite physical
orientation. Selection leaves a doubled zero separator before the source. Both
routines normalize that marker, return through the existing `2.ret1` machinery,
and increase the zero gap before the register file by one cell.

- `movr`, to the physical right, adds seven kernel states. It retains the first
  source one as the new zero source, erases its second one, and fills the old
  source/destination separator. A zero source takes a separate return path.
- `movl`, to the physical left, adds six kernel states. It fills the selected
  separator, scans to the end of the joined run, and separates off its final one
  as the zero source. The split bit is always one, including when the original
  source is zero. Its final erase therefore reuses the existing `1.sel` read-one
  transition. This use does not perform a new register selection.

These counts exclude register-selection chains. A native operation at declaration
index `i` needs the prefix of `i + 1` selector states for that operation kind.
Consequently, good register placement matters even when the instruction tree is
unchanged. The unused third scratch register stays at the far left. The current
implementation does not combine this layout with the separate packed-counter
experiment.

## Search and placement

`search_native.py` combines physical register order and native transfer choices
with decoder live-register allocation, field order, clearing, clause order,
parameter naming, constructor choices, formula syntax and factoring. The present
wide mutation campaign uses right-directed adjacent transfers. Left-directed
kernels are covered by the dedicated sweep and the subsequent tree-preserving
placement pass.

Source candidates receive complete reduction. A width-128 source beam feeds
32 tree finalists, with checked fragment transfer from the pinned 308-state tree.
The inner search screens by exact raw size, fully reduces several leaders each
generation, then fully reduces every retained final tree. Screening can still
miss a source or tree that would improve with more search.

The initial pilot reserved separate ordinary and *configured-native* pools.
Decoder allocation can eliminate a configured transfer; eleven of its sixteen
configured-native finalists emitted no native routine. Its actual transfer
finalists reached 313, while an unused-native configuration reached 311. The
corrected continuation reserves all source slots and all 32 finalists for
**emitted** native routines and deduplicates equivalent source/binding entries.
It starts from five genuine native configurations plus the protected incumbent.

`place_native.py` keeps the optimized instruction tree and changes its native
leaf names to match a new physical layout. Used transfers must form disjoint
directed chains. A subset dynamic program minimizes selector-state count among
orders of those chains and remaining registers, for each uniform orientation.
It retains several tied orders and performs complete table reduction and CFG
checks on each. This is an exact selector-layout optimization within that
construction, not a global optimization of all possible machines. Switching the
best right-transfer trees to the smaller left-transfer kernel reaches 311.
A deeper, width-96 stratified tree search made another 38,400 mutation attempts
and remained at 311.

The recipes, seeds, counts, final scores and selected check results are in
[the curated manifest](../reference/native-experiments.json). The initial tree is
pinned separately so later incumbent changes cannot move these experiments'
starting point. Search outputs and full frontiers remain under ignored `scratch/`.
Each campaign uses one process; the source/tree beam enforces a cooperative
512 MiB resident-memory budget between evaluations. This is not a hard OS limit.

## Exposed register selection and dispatch

The separate address experiment replaces each register-level primitive by a
chain of explicit `1.sel` calls followed by `1.inc` or `1.decnz`. The instruction
search can then share those chains with other tree fragments. Its CFG checker
tracks how many selections are outstanding, resolves the selected logical
register, and rejects missing selections, overflow or unfinished selections at
an exit. Raw hardware increments are not commutable: they consume the selection.

Lowering the incumbent gives 309 states, including one extra dispatcher scanner
state. A width-80, 150-generation search stays at 309. This experiment currently
supports ordinary increments/decrements only, separately from native transfers.

A further probe enumerates all **43,444** primitive-return and jump contexts in
the incumbent's control tree, including register-selector paths. Each attempted
shorter scanner limit, 6 through 1 instead of 7, changes a dispatch result. This
rejects those direct replacements for those control contexts. It does not rule
out a redesigned dispatcher, a different tree or a proof that some contexts are
unreachable from blank tape.

## Checks and reproduction

The expanded native IR replaces every transfer by its original decrement/increment
loop. Complete CFG comparison checks the entire source lowering and every saved
tree, preserving register names, both decrement outcomes and exits. It assumes
the native tape contract; that separate obligation has finite tape checks:

- Random unary tapes vary register count, source/destination values, unrelated
  values, source position and the instruction-pointer gap. Tests check every
  register, tape boundaries and the return position. The verifier runs 2,000
  cases per used direction; the smaller left kernel also passed a 10,000-case
  development sweep.
- A literal blank-tape interpreter compares all ten registers and each dispatched
  operation with an independent atomic-IR execution across 1,024 operations.
  This covers transfers as well as ordinary increments/decrements.
- Saved transfer candidates also receive the existing formula, arithmetic,
  decoder, factoring and final-tree checks, one million smoke steps, and 512
  decrement-boundary comparisons against their own pre-tree source.
- The exposed-address verifier checks table hashes, exact recompilation, full
  reduction, the complete resolved CFG and 1,024 literal atomic operations.

These checks do not prove unbounded tape separation or an end-to-end equivalence
theorem. Lean verification remains deferred. See [verification scope](VERIFICATION.md).

```sh
python3 tools/experiment.py native-pilot
python3 tools/experiment.py native-active
python3 tools/experiment.py native-left
python3 tools/experiment.py native-addresses
python3 tools/experiment.py native-placement
python3 tools/experiment.py native-deep
python3 tools/probe_native.py dispatch
python3 tools/verify_native.py --candidate scratch/replay-native-placement/result.json
python3 tools/verify_native.py --candidate scratch/replay-native-addresses/result.json
python3 -m unittest discover -s tests
```

Placement and deep-tree replays regenerate their recorded prerequisites. Use
`--generations 1` for a smoke run; its result is not a reproduction of the full
campaign. `verify_ics.py` also accepts transfer candidates. Exposed-address
artifacts must use `verify_native.py`, which selects their dedicated builder.

For a new search from the current candidate:

```sh
python3 tools/search_native.py --distinct-sources --output scratch/native.json
python3 tools/place_native.py scratch/native.frontier.json --output scratch/placed.json
```
