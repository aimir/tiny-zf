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

## Verify a changed machine

The [254-state tree variant](../../candidates/mira254-rotation.tm) has also
passed the complete proof with its own literal transition table and
[exact decoder tree](../../candidates/mira254-rotation.tree.json). Its
[verification record](../../reference/mira254-rotation-coq.json) reports all
three endpoints closed. It changes the decoder layout while preserving the
same source interpreter and set theory. Its size equals the upstream record.

After obtaining the pinned checkout above, run from this repository:

```sh
python3 formal/coq/candidate.py --upstream /tmp/zf-reference --coqc coqc \
  --table candidates/mira254-rotation.tm \
  --tree candidates/mira254-rotation.tree.json \
  --output scratch/rotation-proof
```

The output directory must be new. By default this copies the pinned sources
and rebuilds their entire dependency closure, excluding existing compiled
objects. The checked table is written to `scratch/rotation-proof/candidate.tm`;
its bytes must match the committed table. The original upstream files stay
unchanged. To reproduce the named compiler output as well:

```sh
python3 tools/mira_native.py --upstream /tmp/zf-reference \
  --backend contextual --rotate --output scratch/rotation.tm
python3 formal/coq/candidate.py --upstream /tmp/zf-reference --coqc coqc \
  --table scratch/rotation.tm --tree scratch/rotation.tree.json \
  --output scratch/generated-rotation-proof
```

The driver checks the complete blank-tape bootstrap, including every trailing
register, and renumbers states while preserving the identities referenced by
proof lemmas. It generates the decoder definition and a two-way bisimulation
certificate against the unchanged source program. Coq checks the register
excursions, every instruction site, whole-run simulation, the source certificate,
and the complete connection to ZF/ZFC. Neither Python's symbolic executor nor
the generator is an assumed compiler-correctness theorem.

The recorded run reused objects from a freshly rebuilt upstream proof and
recompiled all 15 affected modules, including the three final assumption
audits. `--reuse-upstream-build` enables that faster mode; the default performs
a full source rebuild. The record contains both the generated named-table hash
and `canonical_machine_sha256`, which identifies the committed literal table.
The `zf254_*` theorem names are inherited from the pinned proof; their machine
definition is replaced by the candidate's exact table.

Always pair a machine with its matching tree. The older
`reference/mira254-tree202.json` is a different 202-node layout: pairing it with
this table fails Coq's instruction check. A failed build writes no verification
record. The independent backend in `mira_native.py` also supplies an explicit
compiler and six search transformations; its symbolic results alone are not
formal acceptance.
