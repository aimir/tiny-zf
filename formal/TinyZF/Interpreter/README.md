# Source-interpreter implementation

The fixed target is `Machine308.Halts ↔ Source.Provable 1`. This directory
connects primitive register operations to the numeric source interpreter. It
retains the exact source calculus and requires a proved connection to the
literal machine; compiler correctness is not an assumption.

| Module | Role |
| --- | --- |
| [Structured](Structured.lean) | Defines increment, decrement, sequencing, branches, loops, and scoped exits. Counter induction proves finite loop executions and full register-file postconditions. |
| [Arithmetic](Arithmetic.lean) | Proves destructive copying, clearing, Cantor pairing, Cantor unpairing, and destructive equality testing from primitive loops. Contracts cover arbitrary natural inputs, nonzero destinations where permitted, consumed operands, and untouched registers. |
| [Decoder](Decoder.lean) | Fixes all ten physical register addresses, implements the sixteen-operation proof decoder with primitive loops, and composes it with proof enumeration. |
| [Stack](Stack.lean) | Implements formula-stack pushing, parameter copying, reversed binary payloads, tags, clause selection, and conditional premise popping. Each routine restores both scratch registers. |
| [Graph](Graph.lean) | Checks structured placements against primitive graph instructions and finite jump paths, then proves their execution contracts. Erasing the tape certificate's pointer and space bookkeeping preserves and reflects halting. |
| [Segments](Segments.lean) | Checks increment/jump paths, per-register increment counts, and both decrement branches. Two graphs certified against the same blocks have equivalent unbounded halting. |
| [SourceGraph](SourceGraph.lean) | Generated unoptimized primitive graph. Its data alone do not establish source correctness; the structured placements are required. |
| [Comparison](Comparison.lean) | Generated witnesses pairing 4,162 block boundaries in the candidate and unoptimized graphs. Every witness has passed kernel checking. |

Additional semantic layers are [Expressions](Expressions.lean), which proves
formula construction by structural induction; [SchemaCode](SchemaCode.lean),
which binds all 15 expressions to the independent source schemas; and
[Clauses](Clauses.lean), which proves both inference rules and protected guards.
[Execution](Execution.lean) composes the exact clause order with enumeration,
decoding and the target test. Its whole-iteration contract agrees exactly with `searchStep Source.execute`.

[Placement](Placement.lean) has passed: its phase-by-phase certificates place
the actual structured code in the literal source graph. [Correctness](Correctness.lean)
composes these contracts into unbounded halting equivalence. The
[headline theorem](../../TinyZF.lean) connects that result to the binary tape.

The generated graphs and witnesses are reproducible with
`python3 formal/tools/generate.py`; `--check` compares them without rewriting
files. Generated rows are evidence checked by Lean, not optimizer assumptions
or retained execution logs.
