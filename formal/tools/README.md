# Import and acceptance tools

- `generate.py` imports the 308-state table and the current schema instances,
  selector order and pre-rewrite protected formulas. `--check` compares them byte
  for byte without changing files. It also generates the bootstrap and instruction-graph certificates. Generation does not establish compiler correctness.
- `program_certificate.py` proposes the expanded instruction paths and branch targets used by `generate.py`; the Lean checker validates their literal tape behavior and space requirements.
- `check.py` checks candidate identity and imports, compares the full decoder
  allocation plan, builds the Lean target, checks theorem types and axiom
  dependencies, and checks `verification.json`. `--record` refreshes that compact
  manifest after success.

Run these from any directory using their paths. The canonical instructions are
in [the formal guide](../README.md#run-verification). All generated `.lean` sources
are committed; regeneration requires only Python and the repository's source
tools. Building checks proof terms in Lean. No Coq or solver output is trusted.

`graph_certificate.py` proposes the unoptimized primitive graph and the 4,162
paired increment-segment witnesses used by `Interpreter/SourceGraph.lean` and
`Interpreter/Comparison.lean`. The segment checker verifies every intermediate
edge, the increment multiset, and the final branch targets. The structured-source meaning is checked separately by `Interpreter/Placement.lean`.

The generated machine module includes a balanced transition evaluator with a
kernel proof of equality to the literal table. This speeds certificate checks
without changing the machine definition or its halting proposition. Certificate
rows are checked with literal indices and composed by proved range lemmas;
no execution logs or binary artifacts are generated as proof inputs.

`placement_certificate.py` discovers entries, primitive edges, control-only
jumps, loop back-edges, and exits for each structured interpreter phase. Lean
checks its proposals with `Graph.Models`; the matcher supplies no axioms.
Private placement lemmas correspond to meaningful phases and stay in one file.
