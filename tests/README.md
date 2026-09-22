# Regression tests

Run `python3 -m unittest discover -s tests` from the root. The 23 tests cover:

- Strict table parsing, missing-read totalization and rejected malformed inputs.
- Valid and invalid quotient certificates and local tape-cell preservation.
- Conservative and ICS clause-order restrictions.
- The pinned ICS formula transcription and identity parameter-renaming case.
- 500 safety-guard, 48 detachment and 1,440 constructor differential/arithmetic cases.
- Preservation of the distinguished codes 0 and 1 after formula recoding.
- 4,280 stack/copy/guard/detachment cases for shared arithmetic.
- Closed-block summaries checked against explicit jump resolution.
- Complete factoring CFG equivalence, with negative cases for changed registers,
  replacing halt by return, and removing unconditional divergence.

Exact artifact reproduction and finite tape simulation are separately checked by
`python3 tools/verify_ics.py` and `python3 tools/verify.py`. These commands do not
establish end-to-end formal equivalence with ZF.
