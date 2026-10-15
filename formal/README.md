# Lean verification of the 308-state machine

**The literal binary machine is formally verified against the independently
specified numeric source calculus.** The default build proves this exact theorem
in [TinyZF.lean](TinyZF.lean):

```lean
theorem machine_correct : Machine308.Halts ↔ Source.Provable 1
```

`Machine308.Halts` uses the checked-in table, a two-way infinite all-zero tape,
head position zero, and initial label `0.boot.A`. The machine has 308 working
states; halting is separate. An absent transition also halts. The proof handles
that literal semantics and establishes the invariants needed to exclude
unintended halts during interpreter execution.

`Source.Provable` is an independently stated derivation system: default code 0,
the 15 exact guarded schema instances, detachment, and generalization. It is not
defined as machine execution. The schema definitions expose parameter
permutations, safety guards, Boolean rewrites, and reversed Cantor payloads.
Numeric inputs may be malformed formulas; their behavior is covered too. Code 1
decodes to `v₀ ∈ v₀`.

This theorem proves implementation correctness. The interpretation of this
numeric calculus in a conventional ICS/ZF derivation system, its claimed
relationship to ZF, and the metatheoretic independence conclusion remain outside
the proved statement. None is supplied as a hypothesis or an axiom.

The separate [Coq reference guide](coq/README.md) reproduces the stronger
end-to-end ZF/ZFC theorem for Mira-Cult's 254-state machine. It is the verified
reference for the new optimization search; it does not change this Lean theorem.

## Proof flow

1. [Cantor](TinyZF/Cantor.lean), [Enumeration](TinyZF/Enumeration.lean), and
   [Source](TinyZF/Source.lean) prove arithmetic coding, exhaustive enumeration,
   stack soundness, and compilation of arbitrary source derivations. The source
   enumerator finds code 1 exactly when `Source.Provable 1` holds.
2. [Interpreter](TinyZF/Interpreter/README.md) proves copying, pairing,
   unpairing, formula construction, both inference clauses, protection,
   decoding, and the complete source iteration using only primitive register
   increments/decrements. Checked placements tie that structured code to every
   actual instruction, loop return, and branch in the unoptimized graph.
3. The same directory’s `Comparison` checks 4,162 paired increment/decrement
   blocks relating the unoptimized and optimized graphs. Increment order may
   differ, but every count, register, branch target, and halt is checked. The
   unbounded equivalence follows from a proved progressing simulation.
4. [Tape](TinyZF/Tape/README.md) proves the literal machine’s register
   operations, dispatch, instruction paths, and invariant preservation. Its
   certificate checks all 6,741 instructions. A checked 117-step primitive
   prefix and global instruction-size bound prove sufficient pointer space for
   every later step. Bootstrap checks all 39,769 literal initialization steps.
5. `machine_correct` composes those unbounded equivalences. A positive finite
   implementation of each source step prevents a tape halt from being missed
   between sampled interpreter boundaries.

[Formulas](TinyZF/Formulas.lean) and [Interpretation](TinyZF/Interpretation.lean)
provide the first-order meaning, injective formula coding, total decoding, and
semantic correctness of the chosen protected rewrites. These supporting results
do not assert an equivalence with conventional ZF.

Every theorem has a local explanation. Generated data and their private
certificate batches remain in the corresponding logical module. Batch lemmas
exist to bound elaboration memory; they check all rows and add no assumptions.
The Python compiler, optimizer, matcher, and certificate generators are
untrusted producers. Lean checks their output against the literal definitions.
No alternative or obsolete machine proofs are retained.

## Run verification

With Python 3 and elan installed, from this folder:

```sh
lake exe cache get Mathlib.Tactic
LEAN_NUM_THREADS=1 lake build
python3 tools/check.py
```

The pins are Lean `v4.32.2` and mathlib
`905b95818eb32af7874a58b427f50c1711a5e96c`. The initial cache download needs
network access. All generated Lean sources are committed, so ordinary checking
requires neither regeneration, Coq, nor a solver. Each Lean process is configured
for one worker thread and an 8 GiB allocation ceiling. The large finite
certificates take several minutes to check from scratch.

The acceptance checker builds the default headline, verifies its exact type,
audits principal theorem dependencies, compares every generated import with the
current artifact, checks the decoder plan, and validates the compact
[verification manifest](verification.json). The manifest hashes all Lean sources
recursively. Allowed foundational axioms are only `propext`, `Classical.choice`,
and `Quot.sound`; the audit rejects `sorryAx`, project axioms, and native-computation
axioms. Finite certificate evaluation uses kernel reduction.

After intentionally changing proof sources, run `python3 tools/check.py --record`
to refresh the manifest only after success. For a direct dependency report:

```sh
lake env lean --memory=8192 --threads=1 Audit.lean
```

The [tools guide](tools/README.md) explains regeneration. No logs, binary build
artifacts, or caches belong in Git.

## Reference and remaining mathematical scope

The register/tape decomposition draws on
[Jeffrey Ketchersid’s Coq verification](https://github.com/jeff87654/busy-beaver/tree/4590f221f53151f2b7ca4e7895f1080197ec05c3/ZF/verify),
pinned in [the reference manifest](../reference/coq-verification.json). That
reference verifies other machines and a different source calculus; it is not
an imported theorem or build dependency. No Coq source files are vendored.

The remaining mathematical work is to relate the exact numeric source calculus
to conventional ICS/ZF derivability and then state and prove an independence
result under explicit metatheoretic assumptions. The binary tape-to-source
implementation is fully covered by the headline theorem.
