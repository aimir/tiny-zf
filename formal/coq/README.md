# Verified reference for the 254-state search

Mira-Cult's 254-state machine has a stronger endpoint than our 308-state Lean
theorem: Jeffrey Ketchersid's Coq development proves that it halts from blank
tape exactly when conventional ZF, or ZFC, is inconsistent. We rebuilt the
complete pinned development with Coq 8.20.1 on 15 October 2026. All three
headline theorems reported `Closed under the global context`.

The [upstream headline](https://github.com/jeff87654/busy-beaver/blob/297ab8df7e5de329605c3875b4934643b371a5e3/ZF/m254/coq/e2e/E2E254.v)
is:

```coq
Theorem zf254_halts_iff_ZF  : halts tm c0 <-> ZFc ⊢TC ⊥.
Theorem zf254_halts_iff_ZFC : halts tm c0 <-> (ZFc + AC) ⊢TC ⊥.
Theorem zf254_halts_iff_SIR : halts tm c0 <-> SIR ⊢TC ⊥.
```

The literal table, bootstrap, unbounded register operations, all instruction
sites, source interpreter, proof calculus, and set-theoretic interpretation
are covered. These are Coq theorems about the upstream table; they do not
change the statement of [our Lean headline](../TinyZF.lean).

## Rebuild

Install Coq 8.20.x and Python 3, then obtain the pinned proof sources outside
this repository:

```sh
git clone --filter=blob:none --sparse https://github.com/jeff87654/busy-beaver.git /tmp/zf-reference
git -C /tmp/zf-reference sparse-checkout set ZF/m254 ZF/stdzf ZF/stdzf_r3
git -C /tmp/zf-reference checkout 297ab8df7e5de329605c3875b4934643b371a5e3
python3 formal/coq/check.py --upstream /tmp/zf-reference --coqc coqc
```

Run the final command from this repository's root. The wrapper rejects a
different commit, changed tracked proof sources, a different machine hash,
or a failed theorem audit. The upstream checker recompiles the entire
dependency closure from source, checks the literal table against the machine
file, rejects proof holes, and audits all three theorems' assumptions.
No downloaded compiled proof objects are used. Our clean build took about
11 minutes; build time varies by machine.

An optional `--record /tmp/zf-coq-verification.json` writes a compact record
only after success. Keep compiled objects and build output in the external
checkout. This directory contains the acceptance wrapper and documentation;
the pinned upstream repository supplies the proofs and their dependencies.

The comparison and ongoing optimization work are documented in
[MIRA254.md](../../docs/MIRA254.md). A changed table still needs its own proof:
this successful reference build does not certify a candidate mutation.
