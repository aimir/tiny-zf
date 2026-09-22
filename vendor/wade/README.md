# turing_machine_explorer

Utilities for creating, optimizing and debugging turing machines.

## tmdb.py

Turing machine debugger, loosly based on gdb and pydb.

## zf2.py

Produces a Turning machine with 410 states that halts if it finds an
inconsistency in ZF without regularity or choice. This is a port of zf2.nql in
<https://github.com/sorear/metamath-turing-machines> and
<https://github.com/CatsAreFluffy/metamath-turing-machines>
into a python list based intermediate representation.
This is in turn compiled to a slightly different
register machine than used by NQL.

### usage:

```
$./zf2.py
optimized axiom order: [16, 17, 3, 18, 4, 7, 8, 9, 11, 5, 12, 13, 14, 2, 15, 0, 1, 6, 10, 19]
states count:
framework:    69
decision DAG: 324
total:        393
(tmdb) save zf2.tm
(tmdb) q
```

Other useful tmdb commands are "`break main().0`",
"`c 1000`" (continue past 1000 breakpoints), and "`info tape`".

## TMBuilder.py

A framework for building Turing machines consisting of a register machine
emulator and a decision DAG for the program being compiled. This register
machine is similar to the one in NQL, but there are a few differences:

* The PC is not fixed size and the decision DAG is not constant height.
  I am calling it the IP (Instruction Pointer) instead as it is not really
  a counter anymore.

* The sense of decnz is reversed from decz in NQL: if the decnz is in a car
  the corresponding cdr of the cons will be executed if the register being
  decremented was non-zero.

* The register file as a whole drifts to the right over time.

* Each reg inc/dec requires multiple trips between the IP and register file.
  This enables the per-register overhead to be low at the cost of runtime
  a fairly high constant overhead in states.

There is no check that the IP does not overflow into the register file, and
the initial space provided for the IP is not particularly large. I recommend
running through a few dozen or hundred dispatch cycles and checking that the
space to the register file starts growing. If there are problems, having the
first used registered declared first may help.
