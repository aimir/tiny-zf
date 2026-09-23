# Smaller ZF proof-search Turing machines

**Current experimental candidate: 310 states — 82 fewer than our 392-state baseline (20.9% smaller).**

The candidate combines the corrected ICS axiom formulation with Wade's compiler,
searches axiom order and parameter naming together, reuses one register during
comparisons, and combines a new formula encoding with fused constructors.
Shared stack and copy routines plus a joint source/inlining/factoring search further reduce it.
A further search changes the syntax of the protected UNI and ICS formulas using
classical Boolean identities and quantifier duality. The final dispatcher tree
then saves five states by reassociating instruction blocks and sharing equivalent
increment sequences.
It uses **10 active registers** and **65 framework + 245 instruction-DAG states**.

This is a reproducible experimental machine, **not a formally verified
ZF-independence result**. Lean work is deferred. The mathematical dependency on
the ICS theory's claimed equiconsistency with ZF is stated separately from the
computational checks.

## Results and artifacts

| Machine | States | Artifact and scope |
| --- | ---: | --- |
| Current ICS candidate | **310** | [Table](candidates/ics-best.tm), [configuration and hashes](candidates/ics-best.json), [instruction tree](candidates/ics-tree.json). Changed axiomatization and formula coding; computational checks. |
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
alternative 310-state constructions but no smaller machine; the saved candidate
remains unchanged. [Exact recipes and aggregate results](reference/combined-experiments.json)
cover all three runs. These counts include repetitions, not distinct machines.
A subsequent [pairing/unpairing experiment](docs/PAIRING.md) tested ordinary and
reversed dyadic encodings across **9,909 source evaluations** and **245,760 tree
mutation attempts**. Their best fully reduced results were **321 and 323 states**;
the 310-state incumbent remains unchanged.
[Experiments](docs/EXPERIMENTS.md) explains what worked, what failed, and how to repeat the searches. Search limits are not lower bounds.

## Reproduce and check

Python 3.10 or newer; rebuilding and verification use only the standard library.
Tested with Python 3.14. The optional global search uses OR-Tools.

```sh
python3 tools/verify_ics.py
python3 tools/verify.py
python3 -m unittest discover -s tests
```

The first command rebuilds the 310-state table, checks the ported formulas and
parameter renamings, runs **6,268 local arithmetic/differential cases**, compares
the complete factored register control flow against the rewritten source, checks
the selected formula identities independently, audits the final instruction tree,
and simulates one million literal tape steps. It also compares all ten registers
at **512 decrement boundaries** against the pre-tree source, covering about
12.8 million tape steps per machine. The second checks the conservative 392/393 pair.
The regression suite has **51 tests**, including checks for separate dyadic pairing
experiments. These checks do not establish end-to-end
halting equivalence or the mathematical equivalence of the axiom systems.
[Verification scope](docs/VERIFICATION.md) states the remaining obligations.

Add `--windows` to either verifier to repeat its finite-window reachability
experiment. The tested windows exclude no state/read pairs for either incumbent.

## Continue experimenting

```sh
python3 tools/search_combined.py --workers 2 --edge-rewrites --parent-donors --exploration-slots 4
python3 tools/search_tree.py --stratified --edge-rewrites
python3 tools/experiment.py backend-tree-commute
```

The combined search alternates source changes and tree optimization, keeps
multiple sources with their own saved trees, and ranks survivors by the fully
reduced final machines. It can reuse closed fragments after matching their
register control flow. It defaults to two workers with a cooperative memory budget.

The separate tree search continues from the saved 310-state tree. It screens candidates by
exact raw state count, fully reduces leading candidates, and checks every saved
improvement against the source CFG. The replay command repeats the two stages that led
to 310, starting from the recorded 315-state source. Tree search uses one process
and compacts its working arena each generation.

`tools/solve_tree.py` offers an optional global constraint search over a finite
dictionary of shared instruction sequences. Its bounds concern that model only.
[Tools](tools/README.md) documents both searches and the source-changing searches.

The emitted search `.tm` is the raw compiled table; metadata records both raw
and reduced counts. They are both 310 for the saved candidate. A future result
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
