# Import and acceptance tools

- `generate.py` imports the 308-state table and the current schema instances,
  selector order and pre-rewrite protected formulas. `--check` compares them byte
  for byte without changing files. Generation does not establish compiler correctness.
- `check.py` checks candidate identity and imports, compares the full decoder
  allocation plan, builds the Lean target, checks theorem types and axiom
  dependencies, and checks `verification.json`. `--record` refreshes that compact
  manifest after success.

Run these from any directory using their paths. The canonical instructions are
in [the formal guide](../README.md#run-verification). All generated `.lean` sources
are committed; regeneration requires only Python and the repository's source
tools. Building checks proof terms in Lean. No Coq or solver output is trusted.
