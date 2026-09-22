# Tools

All tools use Python's standard library. Invoke them from the repository root.

| File | Purpose |
| --- | --- |
| `machines.py` | Locate and compile pinned upstream; validate clause orders; strictly read and totalize blank-tape tables. |
| `verify.py` | Rebuild the upstream and candidate tables, check exact equality and structured clause coverage, and run bounded smoke tests. |
| `reduce.py` | Enumerate all local tape branches for short contractions, check exact state quotients, and run finite-window reachability. Adapted from the Riemann project at `c05cef7`. |
| `search.py` | Deterministic beam search over clause orders, scoring the actual final table. |
| `probes.py` | Experimental randomized / estimated-savings factoring and six alternative constant-lowering choices for each of `v_1`…`v_4`. No candidate is promoted automatically. |

To reproduce the initial search:

```sh
python3 tools/search.py --output scratch/order-search.json
python3 tools/search.py --distinct --output scratch/distinct-search.json
```

To reproduce the other probes:

```sh
python3 tools/probes.py grammar --output scratch/grammar-probe.json
python3 tools/probes.py cost --output scratch/cost-probe.json
python3 tools/probes.py lowering --output scratch/lowering-probe.json
```

Both search tools accept `--workers 1` to limit process count. Raw console output
is disposable; curated result JSON contains configurations and aggregate counts.
The emitted search `.tm` contains the raw compiler output. Before promoting any
future reduced table, add and check its transformation certificate.

The experiments preserve the upstream debug-off setting. The vendored compiler
has unexercised error paths (including a missing `reachable()` call in duplicate
sequence handling); the exploratory factoring implementation corrects that call
locally without changing the pinned source.
