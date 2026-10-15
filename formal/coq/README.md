# Coq verification of the 253-state machine

**The [253-state forward-decrement machine](../../candidates/mira253-forward.tm)
halts on blank tape exactly when conventional ZF or ZFC is inconsistent.**
The proof extends Jeffrey Ketchersid's pinned Coq development for Mira-Cult's
254-state machine with a new unbounded decrement kernel. Its source interpreter
and set-theoretic interpretation are unchanged. All three headline theorems
report `Closed under the global context` with Coq 8.20.1.

The [upstream headline](https://github.com/jeff87654/busy-beaver/blob/297ab8df7e5de329605c3875b4934643b371a5e3/ZF/m254/coq/e2e/E2E254.v)
is:

```coq
Theorem zf254_halts_iff_ZF  : halts tm c0 <-> ZFc ⊢TC ⊥.
Theorem zf254_halts_iff_ZFC : halts tm c0 <-> (ZFc + AC) ⊢TC ⊥.
Theorem zf254_halts_iff_SIR : halts tm c0 <-> SIR ⊢TC ⊥.
```

The literal table, bootstrap, unbounded register operations, all instruction
sites, source interpreter, proof calculus, and set-theoretic interpretation
are covered. The inherited theorem names retain `254`, but the candidate build
replaces `tm` with the exact 253-state table. These Coq results do not change
the statement of [our 308-state Lean headline](../TinyZF.lean).

## Rebuild the pinned reference

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

The [253-state table](../../candidates/mira253-forward.tm),
[203-node decoder tree](../../candidates/mira253-forward.tree.json), and
[verification record](../../reference/mira253-forward-coq.json) describe the
current smallest proved machine in this repository. The decoder tree is the
original pinned program. Only the tape-level positive decrement changes.

After obtaining the pinned checkout above, run from this repository:

```sh
python3 formal/coq/candidate.py --upstream /tmp/zf-reference --coqc coqc \
  --table candidates/mira253-forward.tm --halt 253 \
  --tree candidates/mira253-forward.tree.json --decrement-mode forward \
  --output scratch/forward253-proof
```

The output directory must be new. By default this copies the pinned sources
and rebuilds their entire dependency closure, excluding existing compiled
objects. The checked table is written to `scratch/forward253-proof/candidate.tm`;
its bytes must match the committed table. The original upstream files stay
unchanged. To reproduce the two input artifacts independently:

```sh
python3 tools/mira_forward.py --upstream /tmp/zf-reference \
  --output scratch/reproduced-forward253.tm
cmp scratch/reproduced-forward253.tm candidates/mira253-forward.tm
cmp scratch/reproduced-forward253.tree.json candidates/mira253-forward.tree.json
```

The driver checks the complete blank-tape bootstrap, including every trailing
register. The machine reaches its prescribed initial configuration after
**284,880 steps**. It has working states 0 through 252 and undefined terminal
state 253; state names referenced in the register proofs are preserved during
renumbering.

### New decrement proof

Registers are separated runs of ones. Decrement deletes one cell and shifts
all later blocks one position left, appending a zero register. The new routine
carries the gap forward: it fills the previous gap, scans the next run, and
erases that run's final one. A single state handles both the gap and the
transition to the next block. Positive decrement always returns in state 48.

[`forward_decrement.v`](forward_decrement.v) proves the unbounded operation.
`forward_dec_block` carries the gap across one positive run;
`forward_dec` inducts over the arbitrary suffix of registers; `sepsL_forward`
reconciles the tape encodings; and `box_decp` supplies the interpreter contract
for every positive selected register. The remaining helper exposes the final
separator. These are ordinary Coq proofs checked against the literal table.
The driver installs them together with the corresponding symbolic return-state
definition and rebuilds all dependents.

### Complete acceptance chain

The driver generates the decoder definition and a two-way bisimulation
certificate against the unchanged 219-node source program. Coq checks the
register excursions, every instruction site, whole-run simulation, the source
certificate, and the complete connection to ZF/ZFC. Neither Python's symbolic
executor nor the generator is an assumed compiler-correctness theorem.

The candidate checker uses the stronger invariant that the space from the
program-counter marker to the register header is at least **62 cells**. The
literal bootstrap establishes that bound, and the whole-run simulation
preserves it. Coq rebuilds the instruction checks and simulation with this
bound; no additional hypothesis is added to the headline theorems. Use
`--min-gap 40` to reproduce the upstream's more conservative abstraction.

The recorded candidate run reused objects from a freshly rebuilt upstream
proof and recompiled every affected module, including the three final
assumption audits. `--reuse-upstream-build` enables that faster mode; the
default performs a full source rebuild. The record identifies the input and
canonical table, exact tree, replacement proof fragment, pinned sources and
compiled dependency count. A failed build writes no verification record.

### Decoder-layout comparison

The earlier [254-state decoder variant](../../candidates/mira254-rotation.tm)
also has a complete [Coq verification record](../../reference/mira254-rotation-coq.json).
It has its own [202-node tree](../../candidates/mira254-rotation.tree.json) and
uses the original reverse-shifting decrement. Reproduce its proof with:

```sh
python3 formal/coq/candidate.py --upstream /tmp/zf-reference --coqc coqc \
  --table candidates/mira254-rotation.tm \
  --tree candidates/mira254-rotation.tree.json \
  --output scratch/rotation-proof
```

`tools/mira_native.py --backend contextual --rotate` reproduces its named
compiler output when supplied `--upstream` and `--output`. Always pair a table
with its matching tree: `reference/mira254-tree202.json` is a different layout
and fails the instruction check when paired with this table.
