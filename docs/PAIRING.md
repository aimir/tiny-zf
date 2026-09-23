# Pairing and unpairing experiments

**Result: 321 states for ordinary dyadic pairing and 323 for reversed dyadic
pairing. Neither improved the then-current 310-state Cantor incumbent;
the later [decoder search](DECODER.md) reached 308 with Cantor arithmetic.**

| Run | Source evaluations | Tree mutation attempts | Tree evaluations with full reduction | Best source | Best final |
| --- | ---: | ---: | ---: | ---: | ---: |
| Ordinary dyadic | 4,963 | 122,880 | 2,069 | 327 | 321 |
| Reversed dyadic | 4,946 | 122,880 | 1,996 | 329 | 323 |
| Total | 9,909 | 245,760 | 4,065 | | |

Every source evaluation also uses full reduction. Each run optimizes twelve
source finalists; mutation attempts include duplicates. Counts exclude small
smoke runs, an interrupted pilot, and rebuild/verification calls. Observed peak
RSS was 276 MiB and 285 MiB respectively. Arithmetic recoding introduced more
code than source factoring and tree sharing recovered in these bounded searches.
This is evidence against the tested implementations, not a bound on all dyadic
implementations or all pairing functions.

Both winning tables rebuild exactly, pass complete CFG checks against their own
sources, and pass a million literal tape steps plus 512 decrement-boundary
comparisons of all ten registers. The ordinary winner uses a generic tag kernel
with tags `(implication, negation, forall) = (4,2,3)`. The reversed winner uses
fixed tag arithmetic through `scratch1`, with tags `(4,3,2)`.
[Recipes, winning configurations and check summaries](../reference/pairing-experiments.json)
are curated metadata; full frontiers and console logs are not committed.

The incumbent uses Cantor pairing. This experiment implements the dyadic
bijection

```text
D(a,b) = 2^b (2a+1) - 1
```

Its inverse factors `n+1` into a power of two and an odd number. The exponent
is `b`, and `(odd part - 1)/2` is `a`. The implementation uses only
increment and conditional decrement on the existing unary registers.

## Arithmetic and coding contracts

`pair(out,a,b)` starts with `out=0`, consumes both inputs, and leaves the
paired value in `out`. `unpair(a,b,input)` starts with both outputs zero,
consumes `input`, and returns the two components. All three registers must be
distinct. Every other register is preserved, including the unused third
scratch register. No native tape primitive or additional register is introduced.

The ordinary pair implementation initializes `out=2a`, then applies
`out := 2*out+1` exactly `b` times. Induction gives the stated formula. A second
implementation maintains the positive value before subtracting one at the end;
a third alternates the two buffers and copies back only when required at exit.

The ordinary inverse repeatedly consumes two input units into one quotient
unit. An even input returns the quotient; an odd input increments the exponent
and repeats on the quotient. This follows the identities

```text
D(a,0)   = 2a
D(a,b+1) = 2 D(a,b) + 1.
```

The alternative inverse explicitly increments the input and halves until odd.
The inner transfer loops terminate by consuming their source; the outer pairing
loop consumes its exponent, and recursive unpairing strictly decreases its
positive argument. These are mathematical explanations of the intended kernels,
not machine-checked proofs of the generated instructions.

Two complete coding conventions are tested:

| Context | Ordinary | Reversed dyadic |
| --- | --- | --- |
| Stack and proof-field pairs | `D(a,b)` | `D(b,a)` |
| Inner binary formula payload | Same pair convention as stacks | Same pair convention as stacks |
| Outer formula tag | `D(payload,tag)` | `D(payload,tag)` |

The source search independently chooses the order of the inner binary payload.
The reversed dyadic convention changes all generic pairs and unpairs together;
outer formula tags deliberately keep the original orientation. Equality and
membership keep tags 0 and 1; implication, negation and universal quantification
may permute tags 2, 3 and 4 consistently across their constructors.

Consequently the default tautology remains code 0 and the contradiction target
remains code 1. Injectivity of both pairing conventions and distinct outer tags
give injective constructors. For either convention, both unpaired components
are at most the input. The source decrements a nonempty proof tail before
decoding its four fields, so this recoding does not introduce a nonterminating
tail traversal. Connecting the entire enumerator to a formal proof predicate
remains a separate obligation, including treatment of ill-formed numeric codes.

## Search and reproduction

```sh
python3 tools/search_pairing.py --generations 40 --tree-generations 80 --tree-candidates 12
python3 tools/search_pairing.py --dual --seed 20260924 --generations 40 \
  --tree-generations 80 --tree-candidates 12 --output scratch/pairing-dual.json
python3 tools/experiment.py pairing-dyadic
python3 tools/experiment.py pairing-dual
```

Each run starts with a 1,008-configuration grid: three pair kernels, two inverse
kernels, four tag-lowering families, both payload orders, six non-atomic tag
permutations, and the applicable fused/unfused constructor modes. The source
beam then varies formula rewrites, clause order, parameter permutations,
factoring/inlining settings and the arithmetic choices. Every source evaluation
uses the full reduction pipeline. Fingerprints suppress duplicate source trees
in the retained beam; configurations are still counted when evaluated.

The search retains 64 source candidates and optimizes twelve finalists' trees.
Tree search screens by exact raw size, fully reduces its leaders and entire
final frontier, and imports closed fragments from the incumbent only when
their register-control-flow signatures match. Every saved tree must pass the
complete CFG check against its **own recoded source**. The old 310-state tree
cannot stand in for the changed arithmetic. The test suite checks that rejection.

Runs use one process each and compact tree arenas after each generation.
`--memory-mb 512` sets a cooperative process RSS budget, checked between source
evaluations and tree generations; it is not an operating-system hard limit. The
commands above can run sequentially to minimize memory. Scratch artifacts and
frontiers stay under ignored `scratch/`; raw logs are not repository artifacts.
Use `--resume-frontier scratch/pairing.frontier.json` to continue a retained
population. A restart rebuilds the sources and audits trees before accepting
their scores. Search bounds are heuristic, not impossibility results.

## Checking a result

```sh
python3 tools/verify_pairing.py
python3 tools/verify_pairing.py --candidate scratch/pairing.json
python3 tools/verify_pairing.py --candidate scratch/pairing-dual.json --boundaries 512
python3 -m unittest discover -s tests -p test_pairing.py
```

The first command runs numerical kernel contracts and constructor, stack,
protected-guard, proof-field decoder and detachment checks. It compares all registers, not only
the returned integer. Both kernel orientations and all constructor/tag layouts
are covered on bounded inputs. Exponents are deliberately bounded: even modest
dyadic inputs can encode impractically large unary registers.

The candidate command additionally checks table/tree hashes, exact recompilation,
final state counts, chosen formula identities, complete factoring and tree CFGs,
a million literal tape steps and 128 literal decrement boundaries against its
pre-tree source. These backend comparisons stay within one encoding; they do
not compare the recoded arithmetic trace with Cantor arithmetic.

Numerical tests of whole large axiom schemas are impractical with this encoding.
Detachment tests include small actual premise stacks and arithmetic states with
premises already in their registers, so nonzero acceptance and rejection can be
checked without materializing enormous nested stacks. Selected-premise cases
whose encoded stack exceeds 100,000 units are skipped; the exact case count is
reported. The default contract check includes ten detachment cases; the recorded
ordinary and reversed winners cover eight and nine respectively. None of these checks is
a proof of halting equivalence or ZF independence. Use this experiment's dedicated
builder and verifier; the incumbent's `verify_ics.py` checks its Cantor artifact.
