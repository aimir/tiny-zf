# Fused unpairing and tail restoration

This experiment combines source-level unpair/tail fusion, a native tape operation
for the shared arithmetic step, decoder allocation and final-score tree search.
It retains the incumbent's Cantor encoding. Results and exact replay settings are
in [the experiment manifest](../reference/unpair-experiments.json).

**The 308-state incumbent remains unchanged.** The completed searches evaluated
3,998 source configurations and 404,480 tree mutation attempts, including four
whole-tree refinements. All 16 native finalists were also expanded and rescored.

| Construction | Framework | Instruction DAG | Total |
| --- | ---: | ---: | ---: |
| Incumbent | 65 | 243 | **308** |
| Best fused-restoration source | 65 | 243 | 308 |
| Best emitted Cantor kernel | 74 | 239 | 313 |
| Best expanded native tree | 65 | 243 | 308 |

The native winner uses the arithmetic step without fused tail restoration.
Fourteen native finalists had no restoration enabled; two fused theorem selection.
All fusion masks were screened at source level, but the higher-scoring decoder
fusion combinations did not survive the final shortlist. This limits the search's
coverage; it is not evidence that every such combination must be worse.

## Arithmetic contract

Write `C(a,b) = a + (a+b)(a+b+1)/2`. The ordinary unpair routine consumes `n`
while updating two output registers `a,b`. Each iteration performs

```text
if b > 0: (a,b) := (a+1,b-1)
else:     (a,b) := (0,a+1)
```

Each update increases `C(a,b)` by exactly one. If `b > 0`, the sum `a+b` stays
fixed and the first component increases. If `b = 0`, moving to the next diagonal
also adds one to the code. Thus `C(a,b) + n` is invariant when an iteration also
decrements `n`. The input counter decreases strictly until zero. Starting with
zero outputs therefore gives the unique Cantor inverse of the original input.
The same argument handles nonzero initial output registers.

Many callers then transfer `b` back into the now-zero input register. The fused
routine performs this restoration on its input-zero exit, yielding

```text
(a,b,n) = (0,0,z)  →  (first(z),0,second(z))
```

All unrelated registers are preserved. The search can fuse this interface at
three independently controlled sites: proof decoding (mask bit 1), theorem
selection (bit 2), and the protected-axiom guard (bit 4). Decoder fusion requires
an immediately adjacent planned tail transfer; other plans keep their original
sequence. Four equivalent loop arrangements vary the decrement/increment order
and the placement of the diagonal reset. This is an arithmetic argument, not a
Lean-checked theorem.

## Native tape operation

The seven-state `cstep` routine implements the output-pair update directly. Its
two output registers must be the **two rightmost physical registers**: `a` at
declaration index 0 and `b` at index 1. It uses two additional selector states.

The kernel normalizes the doubled selection separator before `b`, shifting the
preceding register prefix by one cell. When `b` is positive, moving the separator
one cell left transfers one unit from `b` to `a`. When `b` is zero, the routine
joins the runs and splits off a new zero `a` register at the tape's right end,
leaving `b = old a + 1`. Both paths share the same final scan and reuse the existing
`1.sel` read-one transition to erase the split bit. That use does not select a
register. The zero gap before the register file grows by one cell.

The rightmost-register restriction is essential: the zero case writes into the
blank cell after `a`. An intervening register would invalidate the routine.
Layout validation enforces the restriction before compilation.

This is a native inner step within a fused unpair routine. The input decrement
and loop dispatch still use the ordinary compiler. It is not a single native
operation that performs an entire unpair call. Full-call tape implementations
also need to route their input and restore a canonical register layout; those
costs are absent from a source-only node-count estimate.

## Search

A width-128 source beam varies arithmetic arrangement, the three fusion sites,
physical register placement, decoder scratch allocation and field order, clearing,
existing adjacent transfers, constructor choices, protected-formula syntax,
clause order and factoring. The source grid contains 190 configurations plus the
protected incumbent. Subsequent mutations receive complete reduction.

The beam reserves 32 slots for loop rearrangements and layout controls, 32 for restored-tail source
variants and 64 for candidates that actually emit `cstep`. Merely enabling the
kernel does not qualify: source rewrites can remove its only call. The final
shortlist contains 8, 8 and 16 candidates from those respective groups.

Every finalist receives checked fragment transfer from the pinned 308-state tree
and its own width-48, 80-generation tree search. Four raw-size leaders per
generation and every final retained tree receive complete reduction. This remains
a heuristic search; its failures are not lower bounds. The engine runs in one
process with a cooperative 512 MiB memory budget, checked between evaluations.

A further run audits all finalists against the entire incumbent tree. It starts
from that 308-state tree only where a complete CFG comparison succeeds and the
source emits no added native kernel. Four sources qualify. Each receives a
width-80, 100-generation search with 192 mutation attempts per generation. This
preserves existing whole-program sharing rather than relying only on transferred
fragments. The original 308-state candidate is protected throughout both runs.

The final expansion pass replaces each native operation in an optimized tree
with its register-level contract, retaining the surrounding tree structure. It
then audits the complete CFG and applies full reduction again. For the best
Cantor candidate this adds four instruction states and removes nine kernel/selector
states, returning to 308. Thus a native operation can serve as an intermediate
search representation even when its literal implementation is more expensive.
These expansions did not beat the incumbent either.

## Verification scope

`check_unpair.py` compares both arithmetic interfaces with the integer Cantor
inverse, including nonzero initial output registers and untouched-register checks.
The literal kernel checker varies register values, prefix length and gap size,
checking the exact resulting register values, separation and return position.
Its development sweep covers 10,000 cases; the full verifier runs 5,000.

A separate source audit expands fused calls back into their original contracts
and compares the entire resulting control-flow graph with the unfused program.
This checks the wiring of every fusion site, assuming the arithmetic contracts.
Increment-first variants also require a direct comparison of the actual expanded
source CFG. Decrement-first variants intentionally have different operation
traces, so their source comparison depends on the arithmetic contracts.

Factoring and final-tree audits compare the actual new instruction program,
including all branches. An independent literal interpreter compares every
register and dispatched operation with an atomic-IR model, including `cstep`.
Decoder checks exercise 1,000 numerical boundaries. The existing formula,
arithmetic, smoke and decrement-boundary checks also run on saved finalists.

Regression tests reject a damaged tape kernel, incorrect arithmetic, a miswired
fusion site, invalid layout and invalid fusion masks. These checks do not prove
unbounded tape separation or end-to-end halting equivalence. These fused/native
kernels are outside the current [Lean verification of the 308-state incumbent](../formal/README.md).
See [verification scope](VERIFICATION.md).

## Reproduce

```sh
python3 tools/experiment.py unpair-fusion
python3 tools/experiment.py unpair-whole-tree
python3 tools/experiment.py unpair-expanded
python3 tools/verify_native.py --candidate scratch/replay-unpair-fusion/result-native.json
python3 tools/verify_native.py --candidate scratch/replay-unpair-fusion/result-restore.json
python3 -m unittest discover -s tests
```

The whole-tree and expansion replays regenerate their source-search prerequisite.
Use `--generations 1` on the replay command for a smoke run; it does not reproduce
the full search. To start a new campaign, use `python3 tools/search_unpair.py`.
The original native search rejects fused-arithmetic records instead of discarding
their settings. The ordinary tree search preserves those settings.

The manifest and pinned input describe the completed experiment. Logs, exhaustive
frontiers and unsuccessful transition tables remain outside Git.
