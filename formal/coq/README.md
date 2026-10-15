# Coq verification of the 251-state machine

**The [251-state machine with shared startup](../../candidates/mira251-startup.tm)
halts on blank tape exactly when conventional ZF or ZFC is inconsistent.**
The proof extends Jeffrey Ketchersid's pinned Coq development for Mira-Cult's
254-state machine with unbounded decrement and increment proofs and a shared
startup routine. Its source interpreter
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
replaces `tm` with the exact 251-state table. These Coq results do not change
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

The [251-state table](../../candidates/mira251-startup.tm),
[203-node decoder tree](../../candidates/mira251-startup.tree.json), and
[verification record](../../reference/mira251-startup-coq.json) describe the
current smallest proved machine in this repository. The decoder tree is the
original pinned program. The tape-level arithmetic and initialization change.

After obtaining the pinned checkout above, run from this repository:

```sh
python3 formal/coq/candidate.py --upstream /tmp/zf-reference --coqc coqc \
  --table candidates/mira251-startup.tm --halt 251 \
  --tree candidates/mira251-startup.tree.json --decrement-mode startup \
  --output scratch/startup251-proof
```

The output directory must be new. By default this copies the pinned sources
and rebuilds their entire dependency closure, excluding existing compiled
objects. The checked table is written to `scratch/startup251-proof/candidate.tm`;
its bytes must match the committed table. The original upstream files stay
unchanged. To reproduce the two input artifacts independently:

```sh
python3 tools/mira_forward.py --upstream /tmp/zf-reference --mode startup \
  --output scratch/reproduced-startup251.tm
cmp scratch/reproduced-startup251.tm candidates/mira251-startup.tm
cmp scratch/reproduced-startup251.tree.json candidates/mira251-startup.tree.json
```

The driver checks the complete blank-tape bootstrap, including every trailing
register. The machine reaches its prescribed initial configuration after
**182,904 steps**. It has working states 0 through 250 and undefined terminal
state 251; state names referenced in the register proofs are preserved during
renumbering.

### Shared startup and increment proof

The initializer uses the existing arithmetic routines, eliminating a dedicated
startup state. It reaches the source enumerator's state `s3`, after three
commands from its initial state: the next-proof counter is 3, the first parameter
register is 1, and the other seven registers are zero. The exact tape has a
40-cell program-counter gap and 95 additional zero registers. The driver proves
the nonhalting step from `s2` to `s3` and uses it to transport the original
halting equivalence; it does not assume that skipping a command is harmless.

Marking now returns uniformly in state 6, and increment shares the decrement
scanner on its return path. [`startup_increment.v`](startup_increment.v)
proves the replacement `shift_inc` lemma by induction on the arbitrary suffix
of registers. Its base case checks the four extra transitions, and its output
connects to the existing state-48 return proof. The local decrement proof below
is unchanged. These universal lemmas justify the shared routines on unbounded
tapes, beyond the finite bootstrap computation.

### General initialization theorem

[`general_initialization.v`](general_initialization.v) separately proves
`clean_state_halts_iff`: the source enumerator halts iff it derives contradiction
from any initial proof-list value, candidate counter and additive parameter,
provided the current formula, cached formula and formula stack are zero.
This permits future initializers beyond a known finite prefix of the original
run. It does not certify a different transition table or tape representation.

Completeness pads the unused suffix of a halting proof program so its numeric
code exceeds the initial counter, and proves that enumeration eventually reaches
that code or halts earlier. Soundness uses the original invariant on the formula
registers and stack. All helper lemmas are documented in the same file.
After rebuilding the pinned reference above, check this auxiliary theorem with:

```sh
mkdir -p scratch/general-initialization
cp formal/coq/general_initialization.v scratch/general-initialization/GeneralInit.v
coqc -Q /tmp/zf-reference/ZF/m254/coq/logic M254L \
  scratch/general-initialization/GeneralInit.v
```

The command must report `Closed under the global context`.
The [verification record](../../reference/mira-general-initialization-coq.json)
identifies the exact source. The published 251-state proof continues to use its
explicit three-command initialization bridge.

### New decrement proof

Registers are separated runs of ones. Decrement deletes one cell and shifts
all later blocks one position left, appending a zero register. The new routine
carries the gap forward by local swaps: it fills the gap, erases the next one,
and moves the gap farther through a run without a separate scanning state.
The loop uses states 112 and 85. Positive decrement always returns in state 48.

[`local_decrement.v`](local_decrement.v) proves `local_dec_ones` by induction
on the run length, then derives `forward_dec_block` for one register block.
The remaining [forward-decrement lemmas](forward_decrement.v) prove the whole
unbounded operation:
`forward_dec` inducts over the arbitrary suffix of registers; `sepsL_forward`
reconciles the tape encodings; and `box_decp` supplies the interpreter contract
for every positive selected register. A padding helper exposes the final
separator. These are ordinary Coq proofs checked against the literal table.
The driver installs them together with the corresponding symbolic return-state
definition and rebuilds all dependents.

### Complete acceptance chain

The driver generates the decoder definition and a two-way bisimulation
certificate against the unchanged 219-node source program. Coq checks the
register excursions, every instruction site, whole-run simulation, the source
certificate, and the complete connection to ZF/ZFC. Neither Python's symbolic
executor nor the generator is an assumed compiler-correctness theorem.

The candidate checker uses the invariant that the space from the
program-counter marker to the register header is at least **40 cells**. The
literal bootstrap establishes that bound, and the whole-run simulation
preserves it. Coq rebuilds the instruction checks and simulation with this
bound; no additional hypothesis is added to the headline theorems. Startup mode
selects this bound automatically and rejects `--min-gap 62`, which its literal
initializer does not establish. The 252- and 253-state modes default to 62;
they also accept `--min-gap 40` for the upstream's more conservative abstraction.

The recorded candidate run reused objects from a freshly rebuilt upstream
proof and recompiled every affected module, including the three final
assumption audits. `--reuse-upstream-build` enables that faster mode; the
default performs a full source rebuild. The record identifies the input and
canonical table, exact tree, replacement proof fragment, pinned sources and
compiled dependency count. A failed build writes no verification record.

### The 252-state local-carry variant

The [252-state table](../../candidates/mira252-local.tm),
[matching tree](../../candidates/mira252-local.tree.json), and
[Coq record](../../reference/mira252-local-coq.json) use the same local decrement
without shared startup. Reproduce its artifacts with generator `--mode local`.
To rebuild its proof, supply these table/tree paths, `--halt 252
--decrement-mode local`, and a fresh output directory to `candidate.py`.
Its bootstrap takes 267,192 steps and reaches `s2` with a 62-cell gap.

### The 253-state block-streaming variant

The [253-state table](../../candidates/mira253-forward.tm) uses a separate
run scanner, with its [matching tree](../../candidates/mira253-forward.tree.json)
and [Coq record](../../reference/mira253-forward-coq.json). To reproduce its
artifacts, pass `--mode forward` to the generator. To rebuild its proof, supply
those table/tree paths, `--halt 253 --decrement-mode forward`, and a fresh
output directory to `candidate.py`. Its bootstrap takes 284,880 steps.

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
