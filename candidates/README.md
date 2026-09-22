# Current candidate

`best.tm` is the literal **392-state** partial transition table; `best.json`
records its clause order and the search that found it. The table uses upstream's
text format and starts on a blank two-way binary tape. No reduction beyond the
compiler is needed to obtain this count.

Run `python3 tools/verify.py` from the repository root to regenerate and compare
it. This is a reproducible candidate, **not a formally verified ZF-independence
result**. See [verification scope](../docs/VERIFICATION.md).
