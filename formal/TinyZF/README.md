# Proof modules

Start with [the headline theorem](../TinyZF.lean), then the
[proof-flow guide](../README.md#proof-flow).

- `Cantor → Enumeration → Source` proves the independently stated source
  interpreter’s soundness and completeness.
- [Interpreter](Interpreter/README.md) implements it using primitive register
  loops, checks the exact structured placements, and relates the optimized graph.
- [Tape](Tape/README.md) implements that graph using the literal transition table,
  proves unbounded invariants, and checks blank-tape initialization.
- `Formulas` and `Interpretation` give first-order meanings and protected-rewrite
  semantics. The conventional ICS/ZF theory bridge remains outside the headline.

Every theorem explains its role locally. Generated tables and certificate
batches are documented beside their checks. `ProtectedOriginal` retains only
five pre-rewrite schemas needed for their semantic comparison. There are no
proof copies for obsolete machines.
