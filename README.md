# Smaller ZF proof-search Turing machines

**251 states, with a complete Coq proof
that it halts on blank tape exactly when ZF or ZFC is inconsistent.**
The [literal table](candidates/mira251-startup.tm),
[matching program tree](candidates/mira251-startup.tree.json),
[verification record](reference/mira251-startup-coq.json), and
[reproduction instructions](formal/coq/README.md#verify-a-changed-machine) are included.
A two-state decrement loop and a shared startup path save three states over
Mira-Cult's pinned 254-state construction. The source program and mathematical
endpoint are unchanged. Initialization reaches exactly the source enumerator's
state after three commands; Coq checks that connection too.

**External benchmark: Mira-Cult's 254-state machine, with an end-to-end ZFC
inconsistency proof in Jeffrey Ketchersid's Coq development.** We have
[rebuilt that complete proof from source](formal/coq/README.md), with all three
headline theorems closed under the global context. Our
[comparison and combined experiments](docs/MIRA254.md) reproduce the architectural
savings, check a 254-state decoder variant, and establish the 251-state
machine by changing the register-operation kernel and removing a startup state.
Its proof uses the 40-cell program-counter capacity supplied by its bootstrap.

**Lean formally verifies the literal 308-state machine: it halts on blank tape
if and only if the independently defined numeric source calculus proves code 1.
The source calculus’s connection to conventional ZF remains unproved.** Start with the
[headline Lean theorem](formal/TinyZF.lean) and [formal verification guide](formal/README.md).

The 308-state ICS candidate combines the corrected axiom formulation with Wade's compiler,
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

The 308-state ICS machine is a reproducible experimental machine, **not a formally verified
ZF-independence result**. The [Lean development](formal/README.md) separates the
proved binary-tape-to-source equivalence from the ICS theory’s claimed
equiconsistency with ZF.

## Results and artifacts

| Machine | States | Artifact and scope |
| --- | ---: | --- |
| Shared-startup machine | **251** | [Table](candidates/mira251-startup.tm), [tree](candidates/mira251-startup.tree.json), [Coq record](reference/mira251-startup-coq.json). Complete blank-tape halting equivalence to ZF/ZFC inconsistency. |
| Local-carry decrement machine | **252** | [Table](candidates/mira252-local.tm), [tree](candidates/mira252-local.tree.json), [Coq record](reference/mira252-local-coq.json). Complete blank-tape halting equivalence to ZF/ZFC inconsistency. |
| Forward-decrement machine | **253** | [Table](candidates/mira253-forward.tm), [tree](candidates/mira253-forward.tree.json), [Coq record](reference/mira253-forward-coq.json). Complete blank-tape halting equivalence to ZF/ZFC inconsistency. |
| Mira-based tree variant | **254** | [Table](candidates/mira254-rotation.tm), [tree](candidates/mira254-rotation.tree.json), [Coq record](reference/mira254-rotation-coq.json). Complete blank-tape halting equivalence to ZF/ZFC inconsistency; equals the external record. |
| Mira-Cult / external benchmark | **254** | [Upstream table and Coq proof](https://github.com/jeff87654/busy-beaver/tree/297ab8df7e5de329605c3875b4934643b371a5e3/ZF/m254); [local comparison](docs/MIRA254.md). Not the machine of this repository's Lean headline. |
| Current ICS candidate | **308** | [Table](candidates/ics-best.tm), [configuration and hashes](candidates/ics-best.json), [instruction tree](candidates/ics-tree.json). Lean-verified tape-to-source equivalence; changed axiomatization and formula coding. |
| Conservative baseline | 392 | [Table](candidates/best.tm), [configuration](candidates/best.json). Same distinct axiom clauses as Wade's source, deduplicated and reordered. |
| Pinned Wade reference | 393 | [Unmodified source/table](vendor/wade/), [provenance](reference/upstream.json). Reproduced transition for transition. |

| Lean result | Scope |
| --- | --- |
| Binary tape to source calculus | Exact blank-tape halting iff `Source.Provable 1`; bootstrap, unbounded register/tape invariants, graph optimization, arithmetic, decoding, and clause execution are proved. |
| Source enumerator correctness | Finds target code 1 iff the explicit numeric source calculus derives 1; arbitrary execution lengths and parameter values. |
| Formula coding and interpretation | Cantor inverses, injective formula encoding, total decoding of malformed inputs, and semantic soundness in source models. |
| Selected formula rewrites | All five protected choices preserve first-order truth in every domain and valuation. |
| Decoder allocation | The exact 16-operation arithmetic plan places all four fields correctly and preserves the counter and theorem stack. |
| Literal machine | The exact 308-state table is imported, identity-checked, and used by the end-to-end proof. |

The headline is `TinyZF.machine_correct : Machine308.Halts ↔ Source.Provable 1`.
[The proof guide](formal/README.md) describes its complete implementation chain.
Compiler correctness is proved for this literal artifact; no compiler or theory
bridge is assumed as an axiom.

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
The [fused-unpair experiment](docs/UNPAIR.md) combines a native Cantor step with
unpair/tail restoration, allocation and separate source/tree search pools. Its
[curated results and replay settings](reference/unpair-experiments.json) include
an additional search seeded with the entire validated incumbent tree. Across
**3,998 source evaluations** and **404,480 tree mutations**, source fusion matched
308; the native kernel reached 313. Expanding all 16 native finalists back into
ordinary instructions also bottomed out at 308.
[Experiments](docs/EXPERIMENTS.md) explains what worked, what failed, and how to repeat the searches. Search limits are not lower bounds.

## Reproduce and check

For the 251-state result, follow the [Coq verification guide](formal/coq/README.md#verify-a-changed-machine).
It rebuilds the proof against the exact committed transition table and program
tree using Coq 8.20.x and pinned upstream sources. The local
[`mira_forward.py`](tools/mira_forward.py) generator with `--mode startup` reproduces both artifacts.

For the Lean development, install elan, then run:

```sh
cd formal
lake exe cache get Mathlib.Tactic
lake build
python3 tools/check.py
```

The acceptance check verifies the exact imports, the headline theorem type,
principal axiom dependencies and all recorded proof-source hashes. It accepts
the full tape-machine theorem while explicitly excluding a ZF-independence claim.
Lean and mathlib are pinned. [Build details](formal/README.md#run-verification).

For the computational checks below, use Python 3.10 or newer from the repository
root; rebuilding and these verifiers use only the standard library.
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
The regression suite includes checks for the external-program importer, Coq acceptance and separate dyadic pairing
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

## Release and citation

The [v0.2.0-experimental release](https://github.com/aimir/tiny-zf/releases/tag/v0.2.0-experimental)
collects the 308-state candidate, its Lean implementation proof, conservative baseline,
pinned upstream sources and reproduction tools.
[CI](https://github.com/aimir/tiny-zf/actions/workflows/verify.yml) checks the Lean
development, exact imports, axiom dependencies, computational verifiers and
regression tests; it does not certify ZF independence.
[CITATION.cff](CITATION.cff) provides release metadata. Please
also credit the upstream work recorded in the provenance manifests and source
survey.
