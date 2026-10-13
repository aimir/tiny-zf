# Proof modules

Read [the headline](../TinyZF.lean) and [the proof-flow table](../README.md#proof-flow)
first. The main chain is `Cantor → Enumeration → Source`; `Formulas` and
`Interpretation` supply the first-order meaning, while `Decoder` verifies the
current arithmetic allocation plan. `Machine → Machine308` defines the literal
tape-machine endpoint but is not yet connected to the source theorem.

Every theorem has a local explanation of its role. `Schemas`, `ProtectedOriginal`
and `Machine308` are generated definitions, not duplicated proof developments.
`ProtectedOriginal` retains only the five pre-rewrite schemas needed to state
the semantic comparison. There are no proof copies for obsolete machines.
