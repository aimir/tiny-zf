# ICS formula source

`zf2.nql` and `LICENSE` are copied without modification from
[CatsAreFluffy/metamath-turing-machines](https://github.com/CatsAreFluffy/metamath-turing-machines/commit/74a0e042f5f0ba433b3161b7c6b35ab319113844),
commit `74a0e042f5f0ba433b3161b7c6b35ab319113844` (17 October 2025).

We port the corrected POW, UNI, ICS and B6a constructor sequences. We retain
Wade's proof enumeration, inference implementations and selection rules; this
is not a compilation or verification of the entire NQL file. In particular,
our DET/GEN clauses remain before the protected phase, with ordinary axioms
following them to reject out-of-range inactive-inference results.

The source's argument that its non-extensional ICS theory is equiconsistent
with ZF is a mathematical dependency, not a theorem proved by this repository.
