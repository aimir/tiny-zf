# Smaller ZF proof-search Turing machines

**Current candidate: 392 states. Reproduced and checked computationally; not formally verified.**

This project surveys and optimizes binary, single-tape machines intended to halt
exactly when ZF is inconsistent. The reference is Andrew James Wade's
[393-state machine](https://codeberg.org/ajwade/turing_machine_explorer/commit/9c5c2e82f6ad5ceb5fb7a2d946aa3b1f1d05b1fce7340fd79029cc9d4756f429),
which we reproduce transition for transition. Its current README still says
410 in the prose; the example and saved machine have 393 states. The older
[linked commit](https://codeberg.org/ajwade/turing_machine_explorer/commit/33b30300054242201a95679aacf7e74312bd8803b0df9a85d2314095efd6804e)
has 432 states and predates a correctness fix.

Our 392-state candidate removes duplicate copies of B6b and B8b and searches the
remaining clause order. Every distinct upstream axiom and inference clause
remains present. The compiler and arithmetic procedures are unchanged. This is
**one state below the reproduced upstream result**; upstream deserves credit
for the reduction from 410 to 393.

## Read first

- [Survey](docs/SURVEY.md): primary sources, past approaches, known defects, and next experiments.
- [Verification scope](docs/VERIFICATION.md): exactly what the checks establish and the missing proof obligations.
- [Candidate](candidates/best.tm) and [reproduction configuration](candidates/best.json).
- [Pinned upstream snapshot](vendor/wade/) and [provenance / file hashes](reference/upstream.json).

## Reproduce and check

Python 3.10 or newer; standard library only. Tested with Python 3.14.

```sh
python3 tools/verify.py
python3 -m unittest discover -s tests
```

The first command checks the snapshot hashes, recompiles both tables, compares
every transition, checks the clause coverage and duplicate claims, recounts the
complete reduction result, and runs bounded blank-tape smoke checks. It does
not prove that the compiler implements the source, that proof enumeration is
complete, or that the source theory is equiconsistent with ZF. There is no Lean
proof in this repository yet.

For the larger reachability experiment:

```sh
python3 tools/verify.py --windows
```

## Search

```sh
python3 tools/search.py --distinct --output scratch/search.json
```

The default is 40 generations, a frontier of 64, 160 new candidates per generation,
and four worker processes. Every candidate is scored after local contraction
and exact state quotienting. Use `--workers 1` for a smaller process footprint.
The saved `.tm` is the raw compiled table; JSON records both raw and reduced
counts. A future result that needs table reduction also needs its reduction
certificate before promotion. The current candidate has 392 in both counts.

The initial survey includes 6,401 evaluated orders for each of the original and
deduplicated programs. The former retained 393; the latter reached 392. See
[experiment records](reference/README.md) and [tool documentation](tools/README.md).
Search limits are experimental budgets, not lower bounds.

## Machine convention

One two-way tape, symbols `0` and `1`, initially all `0`, and one-cell `L`/`R`
moves. Counts exclude the terminal `halt` label. A missing transition also halts.
Upstream has one such missing read, `1.inc` on `1`; this is preserved in the
candidate. The totalized representation used by reduction tools replaces a
missing transition with one extra step to `HALT`, preserving halting existence.

## Attribution and repository contents

The vendored source is unmodified and carries Wade's [MIT-0 license](vendor/wade/LICENSE).
The survey attributes earlier constructions separately. The local reduction
algorithms are adapted from our Riemann workspace at commit `c05cef7`.

Only source, small text tables, curated experiment summaries, and documentation
belong in Git. Raw logs, archives, caches, and generated scratch data are ignored.
