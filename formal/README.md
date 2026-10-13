# Partial Lean formalization of the 308-state construction

**The unbounded numeric source enumerator is proved correct. The literal
308-state machine has been imported, but its source-to-tape simulation and the
ICS-to-ZF connection remain unproved.**

Start with [TinyZF.lean](TinyZF.lean). The default build checks:

```lean
theorem source_enumerator_correct :
    Source.FindsTarget ↔ Source.Provable 1
```

`Source.Provable` is an independently stated numeric derivation system: its
constructors are the default equality code 0, the 15 actual guarded axiom
schemas, detachment and generalization. It is not defined as machine execution.
The schema definitions expose the current permutations, safety guards, Boolean
rewrites and reversed Cantor payloads. Numeric parameters need not already be
well-formed formulas. A total decoder and semantic soundness theorem handle them.

`Source.FindsTarget` means that the source interpreter reaches code 1 after a
positive number of iterations from zero initial registers. Code 1 decodes to
`v₀ ∈ v₀`. Soundness preserves provability of the entire zero-padded theorem
stack. Completeness compiles any derivation into instructions that work above
an arbitrary caller stack, then proves that the counter/tail enumerator
eventually executes that list. Neither direction uses finite test bounds.

The separate definition

```lean
def MachineCorrect : Prop := Machine308.Halts ↔ Source.Provable 1
```

records the remaining tape-machine goal. **There is no theorem proving it yet.**
`Machine308.Halts` uses the exact checked-in table, a two-way infinite all-zero
tape, head position zero and initial label `0.boot.A`. There are 308 working
states; halting is separate. Undefined transitions are retained, including the
missing `1.inc`/`1` case. Establishing that this case is unreachable is part of
the remaining tape invariant, not assumed by the semantics.

## Proof flow

| File | Checked result and role |
| --- | --- |
| [Cantor](TinyZF/Cantor.lean) | Exact diagonal pairing, integer triangular-number formula, both inverse identities and bounds. |
| [Enumeration](TinyZF/Enumeration.lean) | The actual `param1,param3,param2,axiomcode` field order is invertible; every finite instruction list is eventually executed. |
| [Schemas](TinyZF/Schemas.lean) | Imported numeric constructors, all current schema instances and selector order. Definitions, not a compiler proof. |
| [Source](TinyZF/Source.lean) | Stack soundness, compilation of derivations and the unbounded iff theorem. |
| [Formulas](TinyZF/Formulas.lean) | Well-formed syntax, injective encoding, total decoding of all numbers and first-order semantics. |
| [Interpretation](TinyZF/Interpretation.lean) | Source derivations hold in every source model; all selected protected rewrites preserve truth. |
| [Decoder](TinyZF/Decoder.lean) | The exact allocation plan satisfies its boundary contract for all natural register values, assuming its arithmetic operation semantics. |
| [Machine](TinyZF/Machine.lean), [Machine308](TinyZF/Machine308.lean) | Infinite-tape semantics and exact literal transition import with `Fin 308`. |

The rewrite theorem proves semantic equivalence in every domain and assignment.
It does not yet translate Boolean identities into derivations of the fixed
Hilbert calculus. The decoder theorem is about arithmetic contracts; it does not
prove that the physical tape implements unpairing or transfer. These distinctions
are also stated beside the theorems.

## Run verification

With Python 3 and elan installed, from this folder:

```sh
lake exe cache get Mathlib.Tactic
lake build
python3 tools/check.py
```

The pins are Lean `v4.32.2` and mathlib
`905b95818eb32af7874a58b427f50c1711a5e96c`. The first cache fetch needs network
access. No Coq installation, solver or proof-source regeneration is required.

The checker rebuilds the default target, checks the exact theorem type, prints
and checks principal axiom dependencies, compares the literal table and generated
schema imports, checks the current allocation plan, and checks the compact
[verification manifest](verification.json). Allowed foundational axioms are only
`propext`, `Classical.choice`, and `Quot.sound`. It rejects `sorryAx`, added
project axioms and native-computation axioms in the audited dependencies.
No proof logs, binaries or caches are committed.

After intentionally editing proof sources, run `python3 tools/check.py --record`
to refresh the manifest only after all checks pass. For a direct axiom report:

```sh
lake env lean Audit.lean
```

## Coq reference and remaining obligations

The architecture draws on [Jeff's Coq verification](https://github.com/jeff87654/busy-beaver/tree/4590f221f53151f2b7ca4e7895f1080197ec05c3/ZF/verify),
pinned in [the reference manifest](../reference/coq-verification.json). Its
393-state theorem connects Wade's machine to a Tarski-style calculus with
Extensionality, Replacement, Powerset, Union and Infinity. The other checked
machine directories in that reference likewise do not cover this repository's
308-state ICS candidate. The Coq development is a reference for the proof layers;
its theorems are not imported as Lean axioms, and it has not been rebuilt here.
No Coq source files are vendored.

To finish the stronger result, the remaining work is:

1. Relate the actual optimized register program to this source interpreter,
   including arithmetic sharing, clause selection and the final instruction DAG.
2. Verify the tape backend, bootstrap, register-file separation and all halting
   cases for unbounded execution; compose that with the source theorem to prove
   `MachineCorrect`.
3. Connect the explicit numeric source calculus to a conventional presentation
   of the intended ICS theory and formalize the mathematical bridge to ZF.
4. State the metatheoretic assumptions needed for any independence conclusion.

Successful builds currently establish the source theorem and listed components,
not those four remaining obligations.
