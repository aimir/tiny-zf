# Regression tests

Run `python3 -m unittest discover -s tests` from the root. Tests exercise rejected
malformed machine inputs, partial-transition totalization, valid and invalid
quotient certificates, preservation of neighboring cells by local contractions,
and the required axiom-order restrictions.

The real artifact reproduction is separately checked by `python3 tools/verify.py`.
Neither command is an end-to-end formal proof about ZF.
