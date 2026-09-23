# Tools

Rebuilding, verification and beam search use the Python standard library.
The optional global solver needs OR-Tools. Invoke commands from the repository root.

## Current candidate construction

The source flow is **ICS formulas → equivalent protected-formula syntax → parameter naming → comparison storage →
formula constructors/encoding → shared arithmetic → safe inlining and factoring
→ allocated proof-field decoding → an explicit final instruction tree → the unchanged Wade tape backend**.

| File | Role |
| --- | --- |
| `ics.py` | Port the five protected formulas and enforce logical-before-safety phase ordering. |
| `formula_rewrite.py` | NNF-based protected-schema rewrites and an independent Boolean/quantifier-congruence checker. |
| `decoder.py` | Plan live-register use for proof-field decoding, delayed clears, direct writes and packed-counter experiments. |
| `joint.py` | Permute schema parameters, validate configurations and assemble the selected implementation. |
| `storage.py` | Reuse `topwff` as comparison scratch, saving/restoring the theorem at the safety boundary. |
| `constructors.py` | Construct tagged formulas directly with alternative scratch assignments. |
| `encoding.py` | Reverse inner binary payloads while keeping outer tags and formula-stack coding unchanged. |
| `stack_ops.py` | Share selection, stack push/pop and parameter-copy arithmetic. |
| `instruction_tree.py` | Validate/load tree artifacts, model state cost, reassociate blocks and adjust relative jumps. |
| `grammar.py` | Closed-block analysis, inlining, alternative factoring and exact labeled-CFG comparison. |
| `machines.py` | Locate the pinned compiler, validate the conservative baseline, read strict blank-tape tables and totalize partial transitions. |

`build_joint(decode(record), sharing=record.get("shared_operations", False),
grammar=record.get("grammar"), formula_choices=record.get("formula_choices"),
instruction_tree=read_record(record, ROOT / "candidates"), decoder=record.get("decoder"))` rebuilds a complete saved configuration (`read_record` comes from
`instruction_tree.py`; use the configuration file’s directory for search outputs). The unused third scratch name still exists in the inherited
builder, but its operations are absent from the reachable 308-state machine.

## Checking

| File | Role |
| --- | --- |
| `verify_ics.py` | Rebuild the ICS table; check formula transcription, schema renaming, local arithmetic and finite tape execution. |
| `check_decoder.py` | Independently audit symbolic live-value tokens, numerical decoder boundaries and the unchanged inference body. |
| `verify_tree.py` | Audit all branches of the final IR while normalizing consecutive increments; reject altered operations/exits. |
| `tape_check.py` | Compare literal tape executions at decrement boundaries, including all active register values. |
| `verify_sharing.py` | Check 4,280 local sharing cases and audit the complete factored CFG against source. |
| `register_check.py` | Independent interpreter for binary structured register IR and relative jumps; used for local differential tests. |
| `verify.py` | Reproduce the conservative 392/393 pair and check clause coverage. |
| `reduce.py` | All-tape short contractions, exact checked state quotients and finite-window reachability. Adapted from the Riemann project at `c05cef7`. |

```sh
python3 tools/verify_ics.py --windows
python3 tools/verify.py
python3 -m unittest discover -s tests
```

These are computational checks. See [verification scope](../docs/VERIFICATION.md).

## Search and replay

| File | Role |
| --- | --- |
| `experiment.py` | Replay a curated experiment, including its initial configuration and seed. |
| `search_ics.py` | Search clause order within the safety phases. |
| `search_combined.py` | Alternate source changes and tree optimization, reuse checked closed fragments, and select source survivors by final reduced size. |
| `search_decoder.py` | Search allocation, field order and source choices, then fully reduce multiple tree finalists; preserves decoder settings and rechecks resumed trees. |
| `search_pairing.py` | Compare ordinary/reversed dyadic kernels, tag implementations and source layouts, then optimize multiple finalists' trees. |
| `search_tree.py` | Continue tree optimization from the saved artifact; raw screening, full reduction and CFG checks. |
| `solve_tree.py` | Optional OR-Tools model choosing a binary grammar globally within a finite dictionary. |
| `search_rewrites.py` | Joint beam over protected-formula syntax, source layout and factoring seeds. |
| `search_grammar.py` | Joint beam over source and compiler choices; `--preserve-main` keeps the main boundary. |
| `search_joint.py` | Search order, parameter permutations, constructor lowering, comparison storage and payload order; preserve a supplied sharing/factoring configuration. |
| `operators.py`, `search_operators.py` | Independently choose each operator's lowering and exhaust all 2,500 combinations at a fixed layout. |
| `search.py`, `probes.py` | Preserve the original conservative order and factoring experiments. |

```sh
python3 tools/search_decoder.py --output scratch/search.json
python3 tools/experiment.py ics-encoding
python3 tools/experiment.py ics-operators
```

Recorded experiment IDs are `ics-order`, `ics-joint`, `ics-storage`,
`ics-encoding`, `ics-operators`, `ics-sharing`, `ics-grammar-probe`,
`ics-grammar-wide`, `ics-grammar`, `ics-shared-operators` and
`ics-grammar-followup`, `ics-rewrites`, `backend-tree-basic` and
`backend-tree-commute`, `combined-source-tree`, `combined-parent-transfer`,
`combined-wide-screen`, `pairing-dyadic`, `pairing-dual`,
`decoder-allocation` and `decoder-packed-counter`. Use `--workers 1`
for fewer processes in searches that support parallel workers; decoder, pairing and tree
searches use one process. A replay
can use `--generations 1` as a short smoke test, which does not reproduce the full
run. Search outputs go under ignored `scratch/`; raw console traces and beam
frontiers are not committed.

The older joint, grammar, rewrite, operator and combined searches reject records
with a decoder allocation. Use `search_decoder.py` for the current source or
replay their historical recipes. For the older sources they
rebuild its compiler tree and explicitly discard the old tree artifact. They
preserve the supplied arithmetic/formula settings; run `search_tree.py` on their
output to optimize the changed tree, or use `search_combined.py` to alternate both stages automatically. A saved tree must never silently override a
changed source. The dedicated tree search keeps all those source settings fixed. The original `search_ics.py` is an order-only experiment
on the original port; its `--initial` reads only the order.

Source searches score the full local reduction pipeline. Tree search uses an
exact raw-count screen, fully reduces leading candidates (`--screen`, default 4)
and every final frontier candidate, and checks every saved improvement. Its saved
`.tm` is the raw compiler output, with both counts recorded in JSON. The current
candidate needs no post-compilation rewrite. A future reduced artifact needs its
own checked transformation certificate before promotion.

## Alternate source experiments

These modules retain bounded unsuccessful approaches for further research:

- `pairing.py`, `verify_pairing.py`: dyadic pairing kernels, consistent formula/stack recoding, and dedicated numerical/CFG/tape checks. See [pairing experiments](../docs/PAIRING.md) for contracts and commands. They require their own builder and verifier; the incumbent uses Cantor arithmetic.
- `inference.py`: execute only selected inference clauses, allowing destructive parameter use.
- `expression_order.py`: reverse subtree evaluation and consistently recode operator payloads.
- `selected.py`: construct only the selected clause using a structured decision chain.
- `arithmetic.py`: in-place comparison with restoration and destructive selected detachment.
- `grouping.py`: conjoined B6a or POW/UNI clauses and the optional common-witness POW/UNI formula.

They do not participate in the saved candidate. Their `__main__` entry points
report probe counts using curated checkpoints, so they work without old scratch
files. Operator, constructor, storage and encoding modules also provide small
standalone count probes. The experimental branches have no formal equivalence
proof, and stronger mathematical transformations require their own justification.

## Global grammar search

Rebuilding and verification need no solver. The optional `solve_tree.py` requires
OR-Tools; the recorded runs used version 9.15.6755. With that dependency available:

```sh
python3 tools/solve_tree.py --seconds 180 --workers 4
python3 tools/solve_tree.py --seconds 240 --max-states 307 --max-zeros 7
```

Only closed compositions are flattened. Control nodes stay opaque. Candidate
words include the existing grammar, repeated substrings up to `--max-word`
(default 16), and suffixes of required words. Each active word chooses a binary
split; the objective counts dictionary nodes and the required zero-run scanner.
Heights are bounded by 30 in this model. A result or bound is specific to those
restrictions. An improvement is emitted with a tree artifact and checked CFG;
`verify_ics.py --candidate ...` supplies the remaining candidate checks.

Tree search uses one process; solver search defaults to four workers. No raw
frontier, solver model or console log is committed.

## Combined source and tree search

This earlier engine operates on the pre-decoder source. Its recorded runs supply
the correct 310-state starting configuration.

```sh
python3 tools/experiment.py combined-source-tree
```

The outer beam varies protected-formula syntax, clause order, parameter naming,
constructor lowering, payload direction, inlining probability and seed, factoring
method and seed, and whether the main boundary is inlined. A source mutation
always rebuilds its tree. A retained source carries several optimized trees into
its next generation instead of restarting from the compiler output.

Each generation screens new sources by exact raw size and tree fingerprint,
keeps a mixture of good scores and distinct source families, and optimizes each
shortlisted source's tree. Every tree in each final inner frontier receives the
complete reduction pipeline. Source survivors are selected by those final scores;
a smaller subset receives a deeper tree search. The raw screen remains a heuristic:
a source eliminated before tree search could still have produced a better result.
`--exploration-slots 4` exempts four shortlist entries from the raw-size cutoff,
including a diversity preference for other lowering/factoring families.

Closed fragments from the current champion (or the mutation parent with
`--parent-donors`) can transfer to a new source when
canonical register-control-flow signatures agree. Signatures collect consecutive
increments, preserve decrement branch order and distinguish halt from return.
They are conservative: unequal signatures do not prove inequivalence. Transfer
only considers closed fragments with 2–70 DAG nodes and at most 1,500 CFG nodes.
Each retained tree is independently checked against its rebuilt source, and the
saved champion is also audited against the unfactored rewritten program.

The default is two workers. Tree arenas are compacted every generation; discarded
caches are cleared. `--memory-mb 768` is a **cooperative per-worker resident-memory
budget**, checked between tree generations, not an operating-system hard limit.
`--workers 1` reduces concurrency. Raw logs and `.frontier.json` checkpoints belong
under ignored `scratch/` or outside the repository. The emitted `.tm` is the raw
table; a reduced count alone does not qualify a candidate for promotion.

Resume the whole retained population, including each source's optimized trees:

```sh
python3 tools/search_combined.py --initial scratch/combined.json \
  --initial-frontier scratch/combined.frontier.json --parent-donors
```

The restart rechecks all loaded trees against their own rebuilt source. Frontier
files are scratch checkpoints, not curated artifacts or verification evidence.

## Decoder allocation search

```sh
python3 tools/search_decoder.py --generations 40 --tree-generations 80 --tree-candidates 16
python3 tools/search_decoder.py --initial scratch/decoder.json \
  --resume-frontier scratch/decoder.frontier.json
python3 tools/experiment.py decoder-allocation
python3 tools/experiment.py decoder-packed-counter
python3 tools/check_decoder.py
```

The initial grid covers direct destination writes, rotating tail buffers,
eager/delayed clears, transfer order, and deferred parallel assignments. Mutations
also vary field order and the existing source/factoring genes. A liveness planner
rejects destructive aliasing. Source candidates receive full reduction; up to 16
diverse finalists receive tree optimization, complete final-frontier reduction
and independent CFG audits. Tree routines are shared with the pairing search via
an explicit builder argument; this does not substitute dyadic arithmetic.

`--packed-counter` trades a dedicated register for Cantor-packed enumeration
state. `--borrow-stack` temporarily holds the theorem stack in the cleared top
register to reuse the stack unpair routine. These are mutually exclusive and
neither is used in the saved 308-state machine. The search uses one process and a
cooperative `--memory-mb 512` RSS budget. On restart, saved trees are checked and
scored before source selection, so an optimized tree cannot be lost merely
because its compiler-generated tree scores worse. See [contracts and results](../docs/DECODER.md).
