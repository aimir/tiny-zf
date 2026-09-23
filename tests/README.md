# Regression tests

Run `python3 -m unittest discover -s tests` from the root. The 51 tests cover:

- Strict table parsing, missing-read totalization and rejected malformed inputs.
- Valid and invalid quotient certificates and local tape-cell preservation.
- Conservative and ICS clause-order restrictions.
- The pinned ICS formula transcription and identity parameter-renaming case.
- 500 safety-guard, 48 detachment and 1,440 constructor differential/arithmetic cases.
- Preservation of the distinguished codes 0 and 1 after formula recoding.
- 4,280 stack/copy/guard/detachment cases for shared arithmetic.
- Closed-block summaries checked against explicit jump resolution.
- All 268 protected-formula choices, checked independently using Boolean decision diagrams.
- Rejected changes to Boolean meaning, atoms and binders, and malformed rewrite configurations.
- A CFG audit that uses the rewritten source and rejects comparison with the original syntax.
- Complete factoring CFG equivalence, with negative cases for changed registers,
  replacing halt by return, and removing unconditional divergence.

- Final-tree CFG equivalence modulo consecutive increments, with negative tests
  for changed counts/registers, crossing a decrement, changed exits and cycles.
- Tree artifact hashes and rejected cyclic/invalid references.
- Every available single tree rewrite at the incumbent and a closed-word grammar
  round trip, checked independently against the original CFG.
- Equality of all native framework transitions before and after tree optimization.

- Combined-search source mutations cannot silently retain a stale whole-program tree.
- Closed-fragment transfer preserves the changed source's complete CFG.
- Fragment signatures preserve register names, branch order and distinct exits.
- Final-frontier scoring retains an existing optimized tree and source-family diversity.

- Dyadic pair/unpair numerical contracts, both argument orientations, every
  constructor/tag lowering, stack operations, protected guards and proof-field decoding: 28,057
  bounded cases in the default check, including preservation of other registers.
- Dyadic distinguished codes and numerical round trips, invalid tag/alias
  rejection, factoring equivalence, and rejection of the old Cantor tree when
  checking a recoded source.

Exact artifact reproduction and finite tape simulation are separately checked by
`python3 tools/verify_ics.py` and `python3 tools/verify.py`. These commands do not
establish end-to-end formal equivalence with ZF.
