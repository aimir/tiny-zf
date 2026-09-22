# Tools

Python standard library only. Invoke commands from the repository root.

## Current candidate construction

The source flow is **ICS formulas → parameter naming → comparison storage →
formula constructors/encoding → shared arithmetic → safe inlining and factoring
→ the unchanged Wade tape backend**.

| File | Role |
| --- | --- |
| `ics.py` | Port the five protected formulas and enforce logical-before-safety phase ordering. |
| `joint.py` | Permute schema parameters, validate configurations and assemble the selected implementation. |
| `storage.py` | Reuse `topwff` as comparison scratch, saving/restoring the theorem at the safety boundary. |
| `constructors.py` | Construct tagged formulas directly with alternative scratch assignments. |
| `encoding.py` | Reverse inner binary payloads while keeping outer tags and formula-stack coding unchanged. |
| `stack_ops.py` | Share selection, stack push/pop and parameter-copy arithmetic. |
| `grammar.py` | Closed-block analysis, inlining, alternative factoring and exact labeled-CFG comparison. |
| `machines.py` | Locate the pinned compiler, validate the conservative baseline, read strict blank-tape tables and totalize partial transitions. |

`build_joint(decode(record), sharing=record.get("shared_operations", False),
grammar=record.get("grammar"))` rebuilds a complete saved configuration. The unused third scratch name still exists in the inherited
builder, but its operations are absent from the reachable 316-state machine.

## Checking

| File | Role |
| --- | --- |
| `verify_ics.py` | Rebuild the ICS table; check formula transcription, schema renaming, local arithmetic and finite tape execution. |
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
| `search_grammar.py` | Joint beam over source and compiler choices; `--preserve-main` keeps the main boundary. |
| `search_joint.py` | Search order, parameter permutations, constructor lowering, comparison storage and payload order; preserve a supplied sharing/factoring configuration. |
| `operators.py`, `search_operators.py` | Independently choose each operator's lowering and exhaust all 2,500 combinations at a fixed layout. |
| `search.py`, `probes.py` | Preserve the original conservative order and factoring experiments. |

```sh
python3 tools/search_grammar.py --preserve-main --output scratch/search.json
python3 tools/experiment.py ics-encoding
python3 tools/experiment.py ics-operators
```

Recorded experiment IDs are `ics-order`, `ics-joint`, `ics-storage`,
`ics-encoding`, `ics-operators`, `ics-sharing`, `ics-grammar-probe`,
`ics-grammar-wide`, `ics-grammar`, `ics-shared-operators` and
`ics-grammar-followup`. Use `--workers 1` for fewer processes. A replay
can use `--generations 1` as a short smoke test, which does not reproduce the full
run. Search outputs go under ignored `scratch/`; raw console traces and beam
frontiers are not committed.

Every search scores the actual final count after local reduction. Its saved
`.tm` is the raw compiler output, with both counts recorded in JSON. The current
candidate needs no post-compilation rewrite. A future reduced artifact needs its
own checked transformation certificate before promotion.

## Alternate source experiments

These modules retain bounded unsuccessful approaches for further research:

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
