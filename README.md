# Smaller ZF proof-search Turing machines

**Current experimental candidate: 308 states — 84 fewer than our 392-state baseline (21.4% smaller).**

The candidate combines the corrected ICS axiom formulation with Wade's compiler,
searches axiom order and parameter naming together, reuses one register during
comparisons, and combines a new formula encoding with fused constructors.
Shared stack and copy routines plus a joint source/inlining/factoring search further reduce it.
A further search changes the syntax of the protected UNI and ICS formulas using
classical Boolean identities and quantifier duality. The final dispatcher tree
then saves five states by reassociating instruction blocks and sharing equivalent
increment sequences. Joint proof-field decoding and register allocation then save
two more states by delaying clears and changing field order, followed by a new
search of the final instruction tree.
It uses **10 active registers** and **65 framework + 243 instruction-DAG states**.

This is a reproducible experimental machine, **not a formally verified
ZF-independence result**. Lean work is deferred. The mathematical dependency on
the ICS theory's claimed equiconsistency with ZF is stated separately from the
computational checks.

## Results and artifacts

| Machine | States | Artifact and scope |
| --- | ---: | --- |
| Current ICS candidate | **308** | [Table](candidates/ics-best.tm), [configuration and hashes](candidates/ics-best.json), [instruction tree](candidates/ics-tree.json). Changed axiomatization and formula coding; computational checks. |
| Conservative baseline | 392 | [Table](candidates/best.tm), [configuration](candidates/best.json). Same distinct axiom clauses as Wade's source, deduplicated and reordered. |
| Pinned Wade reference | 393 | [Unmodified source/table](vendor/wade/), [provenance](reference/upstream.json). Reproduced transition for transition. |

The upstream README prose still says 410, while its latest pinned table has 393.
The originally linked 2025 commit has 432 states and predates a correctness fix.
See the [source survey](docs/SURVEY.md).

The first ICS round scored **56,264 configurations**. The follow-up scored another **59,176**, targeting
arithmetic sharing and instruction factoring, with every retained candidate
scored after local contraction and exact state quotienting. A third beam scored
**20,481 configurations** combining protected-formula rewrites with source layout
and factoring seeds, reaching 315 states. The subsequent dispatcher-tree search
reached **310**; its recipes and bounded solver experiments are recorded in
[the backend manifest](reference/backend-experiments.json).
A combined source/tree search then evaluated **12,065 source configurations** and
**1,581,312 tree mutation attempts**, with **28,548 full tree reductions**. It found
alternative 310-state constructions but no smaller machine; that round left the then-current 310-state candidate
unchanged. [Exact recipes and aggregate results](reference/combined-experiments.json)
cover all three runs. These counts include repetitions, not distinct machines.
A subsequent [pairing/unpairing experiment](docs/PAIRING.md) tested ordinary and
reversed dyadic encodings across **9,909 source evaluations** and **245,760 tree
mutation attempts**. Their best fully reduced results were **321 and 323 states**;
neither improved the then-current 310-state candidate.
The [decoder/allocation experiment](docs/DECODER.md) reached **308 states**, retaining
16 source finalists for complete tree optimization. Packing the proof counter
into the remaining proof removed a register but finished at 313 states.
The [native-tape experiments](docs/NATIVE.md) combine adjacent transfers, physical
register placement and decoder allocation with width-128 beams and 32 tree
finalists per campaign. Their best transfer result is **311 states**; exposing
register selection to tree search reaches **309**. Neither improves 308.
[Experiments](docs/EXPERIMENTS.md) explains what worked, what failed, and how to repeat the searches. Search limits are not lower bounds.

## Reproduce and check

Python 3.10 or newer; rebuilding and verification use only the standard library.
Tested with Python 3.14. The optional global search uses OR-Tools.

```sh
python3 tools/verify_ics.py
python3 tools/verify.py
python3 -m unittest discover -s tests
```

The first command rebuilds the 308-state table, checks the ported formulas and
parameter renamings, runs **6,268 local arithmetic/differential cases**, compares
the complete factored register control flow against the rewritten source, checks
the selected formula identities independently, audits the final instruction tree,
audits decoder register allocation, checks **1,000 decoder boundaries**, and
simulates one million literal tape steps. It also compares all ten registers
at **512 decrement boundaries** against the pre-tree source, covering about
12.8 million tape steps per machine. The second checks the conservative 392/393 pair.
The regression suite has **75 tests**, including checks for separate dyadic pairing
experiments. These checks do not establish end-to-end
halting equivalence or the mathematical equivalence of the axiom systems.
[Verification scope](docs/VERIFICATION.md) states the remaining obligations.

Add `--windows` to either verifier to repeat its finite-window reachability
experiment. The earlier 310-state and conservative-baseline window experiments excluded no
state/read pairs; windows have not been rerun for the 308-state candidate.

## Continue experimenting

```sh
python3 tools/search_decoder.py --generations 40 --tree-generations 80 --tree-candidates 16
python3 tools/search_tree.py --stratified --edge-rewrites
python3 tools/experiment.py decoder-allocation
python3 tools/search_native.py --distinct-sources
```

The decoder search varies field order, scratch placement, transfers, clearing,
source layout and factoring. It fully reduces source candidates, then optimizes
multiple finalists using checked fragment transfer and fully reduced tree scores.
It runs in one process with a cooperative 512 MiB memory budget. Saved trees are
rechecked and scored when resuming a frontier.

The separate tree search continues from the saved 308-state tree while holding
the source fixed. The replay command repeats the decoder campaign from its pinned
310-state starting configuration. Older source searches reject decoder records
rather than silently discard their allocation settings; their historical recipes
still work with the recorded inputs.

`tools/solve_tree.py` offers an optional global constraint search over a finite
dictionary of shared instruction sequences. Its bounds concern that model only.
[Tools](tools/README.md) documents both searches and the source-changing searches.

The emitted search `.tm` is the raw compiled table; metadata records both raw
and reduced counts. They are both 308 for the saved candidate. A future result
that relies on table reduction needs a checked reduction certificate before
promotion. [Tools](tools/README.md) documents the implementation.

## Convention and attribution

One two-way tape, symbols `0` and `1`, initially all `0`, one-cell `L`/`R` moves.
State counts exclude the terminal `halt` label. A missing transition also halts;
the missing `1.inc`/`1` read is preserved. The reduction representation replaces
missing transitions by one extra step to `HALT`, preserving halting existence.

The unmodified Wade snapshot carries its [MIT-0 license](vendor/wade/LICENSE).
The corrected ICS formula source carries its [MIT license](vendor/cats/LICENSE).
Local reduction algorithms are adapted from our Riemann workspace at `c05cef7`.
Only source, small text tables, curated configurations/results and documentation
belong in Git. Raw logs, archives, caches and search frontiers are excluded.
