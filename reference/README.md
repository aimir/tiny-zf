# Reference and experiment summaries

These are small, curated metadata files, not execution logs or exhaustive search
traces. All final counts include the local reduction pipeline.

| File | What it records |
| --- | --- |
| [upstream.json](upstream.json) | Exact source commit, file hashes, reference order, and 393 = 69 + 324 state split. |
| [history.json](history.json) | Recent upstream commit dates and counts of their saved transition tables. |
| [checks.json](checks.json) | Rebuild checks, bounded simulations, regression count, and reachability-window summary. |
| [order-search.json](order-search.json) | 6,401 orders of the original 20-clause program: best 393. |
| [../candidates/best.json](../candidates/best.json) | 6,401 orders with duplicate copies removed: best 392. |
| [grammar-probe.json](grammar-probe.json) | 2,000 randomized factoring seeds: best 393. |
| [cost-probe.json](cost-probe.json) | 200 estimated-savings factoring seeds: best 395. |
| [lowering-probe.json](lowering-probe.json) | All 1,296 combinations of six constructor lowerings for four constants: best 393. |

The two beam runs and three probe runs total **16,298 scored configurations**;
this includes each beam's initial configuration and does not imply that every
compiled transition table is distinct. Randomized factoring changes source
traversal order, while the constant probe changes nesting of the same pushes and
increments. These are bounded experiments, not optimality proofs.

[Tool documentation](../tools/README.md) gives the reproduction commands. The
one-million-step smoke checks enter the main dispatch 1,037 times for each
machine. They do not exercise an unbounded proof search or prove tape separation.

## ICS round: 23 September 2026

| File | What it records |
| --- | --- |
| [ics-upstream.json](ics-upstream.json) | Corrected ICS source commit and hashes. |
| [ics-experiments.json](ics-experiments.json) | Exact initial/final configurations and budgets for twelve replayable runs: 56,264 initial, 59,176 sharing/factoring and 20,481 formula-rewrite configurations. |
| [backend-experiments.json](backend-experiments.json) | Dispatcher-tree search recipes and bounded backend/constraint experiments. |
| [combined-experiments.json](combined-experiments.json) | Three combined source/tree recipes, 12,065 source evaluations, 1,581,312 tree mutation attempts, and aggregate checks; best for those runs was 310. |
| [combined-initial-tree.json](combined-initial-tree.json) | Exact 310-state starting tree for replay; its source and hash are in the combined manifest. |
| [pairing-experiments.json](pairing-experiments.json) | Two dyadic-pairing recipes, 9,909 source evaluations, 245,760 tree mutation attempts, and winning configurations/check summaries; results 321 and 323. |
| [decoder-experiments.json](decoder-experiments.json) | Decoder allocation and packed-counter recipes, counts, winning configurations and check summaries; results 308 and 313. |
| [native-experiments.json](native-experiments.json) | Native transfer/allocation beams, exact selector placement, exposed-address and dispatch probes, replay recipes and aggregate checks; the incumbent stays 308. |
| [native-initial-tree.json](native-initial-tree.json) | Pinned 308-state tree used to seed native experiments; configuration and hash are in the native manifest. |
| [unpair-experiments.json](unpair-experiments.json) | Fused unpair/tail restoration, native Cantor-step and whole-tree replay settings, final counts and selected verification results. |
| [ics-checks.json](ics-checks.json) | Curated rebuild, local differential, finite simulation and reachability results for the 308-state table (without a new window experiment). |
| [../candidates/ics-best.json](../candidates/ics-best.json) | Current 308-state candidate configuration, table hash and state breakdown. |
| [coq-verification.json](coq-verification.json) | Pinned Coq reference and inspected proof layers; reference only, not rebuilt or imported as Lean axioms. |
| [../formal/verification.json](../formal/verification.json) | Checked Lean source hashes, headline, axiom dependencies and explicit incomplete end-to-end status. |

These add to the initial survey experiments above. Full generation traces and
beam frontiers are intentionally absent. Use `python3 tools/experiment.py ID` to
replay a run; see [the experiment report](../docs/EXPERIMENTS.md).
