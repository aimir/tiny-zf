# Survey: ZF-independent Turing machines

Updated 15 October 2026. State counts below distinguish published claims,
locally counted tables, and exact local reproduction. None is a lower bound.
The smallest table inspected here is Mira-Cult's **254-state** machine, with
Ketchersid's external end-to-end Coq proof to ZFC inconsistency. Our **308-state**
ICS candidate has a Lean proof of tape-to-source equivalence; its source theory
bridge to conventional ZF remains open. See the [254-state comparison](MIRA254.md)
and [local experiments](EXPERIMENTS.md).

## Sources and development lines

| Construction | Size | What to take from it |
| --- | ---: | --- |
| [Mira-Cult, September 2026; Ketchersid verification](https://github.com/jeff87654/busy-beaver/tree/297ab8df7e5de329605c3875b4934643b371a5e3/ZF/m254) | **254** | New logical basis, proof enumeration, four-tag coding, single-marker interpreter and contextual sharing. Coq theorem to conventional ZF/ZFC inconsistency; see the dedicated comparison for local checks. |
| [Yedidia–Aaronson, 2016](https://arxiv.org/abs/1605.04343) | 7,910 | Laconic compilation and introspective encoding; the original construction uses a stronger-theory/combinatorial route. |
| [O'Rear, 2016](https://github.com/sorear/metamath-turing-machines/blob/master/machines/2016-zf-sorear-1919/zf.nql) | 1,919 | Direct search for a contradiction in set theory. |
| [O'Rear, 2017](https://github.com/sorear/metamath-turing-machines/blob/master/machines/2017-zf-sorear-748/zf2.nql) | 748 | Detailed source-level explanation of the predicate calculus, set axioms, pairing, and proof enumeration. |
| [Riebel, 2023, §§3.5–3.6](https://www.ingo-blechschmidt.eu/assets/bachelor-thesis-undecidability-bb748.pdf) | 745 | Analysis of pairing, formula construction, peepholes, and failed approaches. The thesis expressly leaves compiler verification open. |
| [Ridenour / CatsAreFluffy, July 2024](https://github.com/CatsAreFluffy/metamath-turing-machines/commit/75ab179) and [August 2024](https://github.com/CatsAreFluffy/metamath-turing-machines/commit/6fc33bef6ba8885d26aed94c83e88bdabbedb0f1) | 643 → 636 | A different axiomatization and NQL/compiler improvements. Historical counts, subsequently subject to corrections. |
| [Wade, July 2025](https://github.com/andrew-j-wade/metamath-turing-machines/commit/30d2e3194866615f68dd2f5101cb300fb039adca) and [alignment follow-up](https://github.com/andrew-j-wade/metamath-turing-machines/commit/5d676aec074a94f598959cb3b7733a8f7781762f) | 588 → 549 | Removing no-op transitions and changing instruction alignment in the NQL backend. |
| [Wade, August 2025](https://codeberg.org/ajwade/turing_machine_explorer/commit/33b30300054242201a95679aacf7e74312bd8803b0df9a85d2314095efd6804e) | 432 | Python structured program and decision-DAG register-machine backend; returns to O'Rear's axiom system. Saved table counted locally. |
| [Wade, August 2026](https://codeberg.org/ajwade/turing_machine_explorer/commit/9c5c2e82f6ad5ceb5fb7a2d946aa3b1f1d05b1fce7340fd79029cc9d4756f429) | 410 → 406 → 405 → **393** | Bootstrap/register redesign, dispatch based on limited zero runs, constant lowering, then axiom ordering. Current 393 table reproduced exactly. |

The complete commit IDs, dates and saved-table counts for the recent Wade line
are in [history.json](../reference/history.json). These source histories are
more informative than the stale headline prose in the current upstream README.
The source commit dates also place the 748 machine in 2017 and the 636 change
in August 2024; some secondary histories differ.

A separate [CatsAreFluffy branch](https://github.com/CatsAreFluffy/metamath-turing-machines/commit/74a0e042f5f0ba433b3161b7c6b35ab319113844)
ended at a claimed **629 states** in October 2025 after several corrections.
It drops Extensionality as well as Regularity and Choice, and combines Infinity,
Collection and Separation into an **ICS scheme**, retaining Powerset and Union.
Its source sketches an interpretation through a constructible universe. This is
a distinct logical development, not an obsolete version of Wade's current
393-state program. The experimental port to Wade's newer backend now reaches 308 states; see
[the follow-up experiments](EXPERIMENTS.md). The equiconsistency argument still
needs scrutiny before this could replace the conservative baseline as a verified result.

[Matthew House's 372-state construction](https://github.com/LegionMammal978/turing_machine_explorer/blob/main/pa.py)
targets **Peano arithmetic**, using an adjunction/separation scheme. It is not
a smaller machine for the same ZF task. The associated
[interpretation discussion](https://mathoverflow.net/questions/508137/interpreting-pa-with-only-adjunction-separation/508161)
is relevant when considering alternative theories, not as a ZF record.

## What the upstream 393-state program actually does

The mathematical source is a modified Tarski-style predicate calculus plus
Extensionality, Replacement/Separation, Powerset, Union and Infinity. Regularity
is omitted; Choice is not added. Formula trees, proof stacks and candidate
proofs are encoded by natural numbers using a Cantor pairing function. Arithmetic
runs on **11 unary registers**, rather than the nine in the Riemann project.
The distinguished target formula is the code for `v₀ ∈ v₀`. Its *provability*
would imply inconsistency; merely exhibiting a self-membered set in a theory
without Regularity is a different statement.

The backend has a **variable-length instruction pointer** and a shared binary
instruction DAG. There is no fixed 11-bit program counter to shorten. Each DAG
node contributes a machine state; register selection and the arithmetic
interpreter move between the instruction pointer and a register file that
drifts right. The reference splits into **69 framework states + 324 DAG states**.
Thus changing instruction sharing is a larger immediate target than shaving a
few bits from a fixed-width address that this machine does not have.

The main source has 20 selectable clauses, but B6b and B8b each occur twice.
The local verifier compares their fully expanded structured source, and checks
that deduplication retains all 18 distinct clauses. Upstream already searches
axiom order by greedily exchanging adjacent blocks. Our search retains a wider
frontier and accepts sideways candidates, with the full final machine count as
its objective.

## Correctness findings that affect the baseline

- The user's linked 432-state commit predates a
  [B6a register-restoration fix](https://codeberg.org/ajwade/turing_machine_explorer/commit/10fcf152b34d0d4677dff737da0b2da34392fe1481c81d0957f57c0aab12336d).
  Two copies of `param3` were restored into `param1`. The fixed count stayed 432.
- DET and GEN must not be the last selectable clause. Upstream explains that
  otherwise out-of-range selector values can admit bogus formulas when premise
  loading is skipped. Our order validator enforces this restriction.
- The CatsAreFluffy line contains explicit fixes in
  [September 2025](https://github.com/CatsAreFluffy/metamath-turing-machines/commit/ed63846246ce8529b387bd634878c92f1cf860e5),
  [later September](https://github.com/CatsAreFluffy/metamath-turing-machines/commit/c5735f9),
  and [October](https://github.com/CatsAreFluffy/metamath-turing-machines/commit/74a0e042f5f0ba433b3161b7c6b35ab319113844): parameter safety, the ICS formula, and B6c.
  These do not automatically imply the same bugs exist in Wade's different source.
- Wade's README explicitly leaves instruction-pointer/register-file collision
  unchecked. Finite simulation can catch an early collision; it cannot prove
  absence of collisions forever.
- The upstream table has an undefined `1.inc`/`1` transition as well as edges to
  `halt`. A source-to-machine proof must rule out unintended undefined-transition
  halts on reachable configurations. The importer must not silently discard them.

## Initial experiments

See [the experiment index](../reference/README.md) for commands and saved summaries.
The **392-state candidate** changes only clause selection: omit the extra copies
at indices 6 and 7 and use the recorded 18-clause order. Its backend and register
operations are byte-for-byte the pinned upstream implementation.

Plain local contractions of lengths 3, 5 and 7 and exact transition quotienting
leave both the 393 reference and 392 candidate unchanged. Seven finite-window
reachability analyses of the reference retain all 786 state/read pairs, even
with over a million abstract configurations in one window. Consequently this
abstraction does not expose useful unreachable branches for further merging.
This is evidence about this abstraction, not a lower bound on equivalent TMs.

The first 6,401-order search with all 20 clauses retained 393. Deduplication plus
6,401-order search reached 392, with no further decrease over 40 generations.
The frontier width was 64, rather than a single greedy incumbent. We also
experimented with randomized common-subsequence extraction, estimated-savings
factoring, and constant-constructor nesting; their measured results are indexed
with the other experiments.

## Best next directions

1. **Continue auditing and optimizing the ICS port.** The experimental port now
   reaches 308 states; see [the follow-up](EXPERIMENTS.md). Combining a smaller logical
   representation with the newer backend might yield much more than another
   permutation search. Preserve a separate theory definition and establish its
   consistency-strength relationship; do not silently change the target theory.
2. **Expand the constructor/grammar search space.** The current candidate already
   searches source layout and inlining together. Add larger arithmetic fragments,
   respecting the relative `break`/`continue` semantics. Merely flattening a
   structured program is not a valid compiler transformation.
3. **Use phase and register invariants.** A semantic analysis can justify consuming
   parameters after their last use and sharing scratch registers. This may expose
   savings that tape-window analysis misses. Couple it to a proof of sufficient
   instruction-pointer space.
4. **Preserve the proved backend/source contract during further rewrites.**
   The [Lean headline](../formal/TinyZF.lean) now connects the literal 308-state
   machine to its independent source calculus. New candidates must supply their
   own checked certificates and preserve that fixed statement.

## The independence claim

The intended first theorem is that blank-tape halting is equivalent to existence
of a finite contradiction proof for the specified source theory. Its relationship
to ZF then uses an equiconsistency result and a formalizable proof translation.
Under consistency of ZF, Gödel's second incompleteness theorem prevents ZF from
proving the resulting nonhalting statement. Claiming that ZF cannot prove halting
either requires an additional soundness assumption, for example Σ₁-soundness;
mere consistency should not silently be used for both directions.
[Aaronson's Busy Beaver survey](https://www.scottaaronson.com/papers/bb.pdf)
discusses the proof-search construction and these metamathematical connections.
See [Verification](VERIFICATION.md) for what has actually been established here.
