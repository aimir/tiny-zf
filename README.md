# Smaller ZF proof-search Turing machines

**Current experimental candidate: 339 states — 53 fewer than our 392-state baseline (13.5% smaller).**

The candidate combines the corrected ICS axiom formulation with Wade's compiler,
searches axiom order and parameter naming together, reuses one register during
comparisons, and combines a new formula encoding with fused constructors.
It uses **10 active registers** and **67 framework + 272 instruction-DAG states**.

This is a reproducible experimental machine, **not a formally verified
ZF-independence result**. Lean work is deferred. The mathematical dependency on
the ICS theory's claimed equiconsistency with ZF is stated separately from the
computational checks.

## Results and artifacts

| Machine | States | Artifact and scope |
| --- | ---: | --- |
| Current ICS candidate | **339** | [Table](candidates/ics-best.tm), [configuration and hash](candidates/ics-best.json). Changed axiomatization and formula coding; computational checks. |
| Conservative baseline | 392 | [Table](candidates/best.tm), [configuration](candidates/best.json). Same distinct axiom clauses as Wade's source, deduplicated and reordered. |
| Pinned Wade reference | 393 | [Unmodified source/table](vendor/wade/), [provenance](reference/upstream.json). Reproduced transition for transition. |

The upstream README prose still says 410, while its latest pinned table has 393.
The originally linked 2025 commit has 432 states and predates a correctness fix.
See the [source survey](docs/SURVEY.md).

The new round scored **56,264 configurations** after local contraction and exact
state quotienting. [Experiments](docs/EXPERIMENTS.md) explains what worked, what
failed, and how to repeat the searches. Search limits are not lower bounds.

## Reproduce and check

Python 3.10 or newer; standard library only. Tested with Python 3.14.

```sh
python3 tools/verify_ics.py
python3 tools/verify.py
python3 -m unittest discover -s tests
```

The first command rebuilds the 339-state table, checks the ported constructor
sequences against the pinned source, checks parameter renamings, runs 1,988 local
arithmetic/differential cases, and simulates one million literal tape steps.
The second checks the conservative 392/393 pair. The regression suite has
16 tests. These checks do not establish end-to-end halting equivalence or the
mathematical equivalence of the axiom systems. [Verification scope](docs/VERIFICATION.md)
describes the remaining obligations.

Add `--windows` to either verifier to repeat its finite-window reachability
experiment. The tested windows exclude no state/read pairs for either incumbent.

## Continue experimenting

```sh
python3 tools/search_joint.py --storage --encoding --output scratch/search.json
python3 tools/experiment.py ics-encoding
```

The first starts a new joint search from the current candidate. The second
replays the recorded encoding search from its original configuration and seed.
Other recorded runs are `ics-order`, `ics-joint`, `ics-storage`, and `ics-operators`.
Use `--workers 1` for a smaller process footprint. Defaults use four workers;
no Lean build or large solver is required.

The emitted search `.tm` is the raw compiled table; metadata records both raw
and reduced counts. They are both 339 for the saved candidate. A future result
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
