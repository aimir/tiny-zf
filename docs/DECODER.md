# Proof decoding and register allocation

**Result: 308 states, down from 310.** The saved machine uses ten active
registers, with 65 framework states and 243 instruction-tree states. Both the raw
compiler output and complete local reduction have 308 states.

The winning decoder reads fields in the order `param1, param3, param2, axiomcode`.
Each unpair still uses the shared `scratch1, scratch2, prooflist` kernel. It moves
the remainder back to `prooflist`, clears the destination field, and moves the
head into that destination. Previously all four destinations were cleared before
any decoding. The reordered operations admit a smaller shared instruction tree.
Direct destination writes and more aggressive register borrowing were explored,
but are not present in this winner.

## Register contracts

Between instructions, `nextproof`, `topwff` and `wffstack` are live. The four old
field values are dead, `prooflist` holds the remaining proof, and `scratch1` and
`scratch2` are zero. The allocator in `tools/decoder.py` tracks these distinctions
while choosing the destinations of four destructive unpairs.

- Unpair consumes one tail into two distinct zero registers.
- Clear can discard an old field value, but cannot destroy a live decoded field.
- Destructive transfer requires a zero destination and clears its source.
- At exit the four named fields contain their decoded values, `prooflist` contains
  the remaining tail, and both scratch registers are zero. Other registers are
  unchanged by the allocation plan.

Destinations can receive heads directly; tail buffers can rotate between stages.
The deferred mode holds extracted heads in temporary locations until all four
splits finish, then performs a parallel assignment, using a free zero register to
break cycles. The same plan is audited independently with symbolic value tokens.
The checker assumes the existing unpair/transfer contracts; it does not constitute
a kernel-checked proof of the generated register or tape code.

Two additional modes were implemented and boundary-tested. `--borrow-stack`
pushes the old top theorem before decoding, temporarily stores the packed theorem
stack in the cleared top register, and decodes through `wffstack` to share its
unpair kernel. Small source probes were larger, so it did not receive a full
campaign. `--packed-counter` represents persistent enumeration state as
`Cantor(nextproof, remaining_proof)`. After the default theorem push it unpacks the
counter into the cleared top register, performs decoding, and repacks before
entering the inference body. This removes the dedicated physical `nextproof`
register, giving nine active registers. Extra instruction machinery outweighed
that saving in the completed campaign. The two modes cannot be combined because
both borrow the top register for different live values.

## Proof coding

The arithmetic remains

```text
C(a,b) = a + (a+b)(a+b+1)/2.
```

For a field order `(f1,f2,f3,f4)` and a remaining tail `t`, one instruction's
numeric code is `C(f1,C(f2,C(f3,C(f4,t))))`. Cantor pairing is bijective, and
permuting the four field names preserves the set of represented instruction
tuples. A positive continuation stores one plus the next instruction's code;
the enumerator decrements it before decoding. Each tail is at most its input, so
this positive continuation decreases strictly during traversal. For any finite
instruction sequence, nested pairing and this positive-tail convention construct
a code for that sequence.

Changing field order changes which numeric proof codes represent which sequences.
It does not change the formula constructors, inference clauses or contradiction
target. Connecting these coding facts to soundness and completeness of the full
stack-based enumerator is still a formal proof obligation. The current result has
computational checks, not a ZF-independence theorem.

## Completed searches

| Run | Source evaluations | Tree mutation attempts | Full tree reductions | Best source | Best final |
| --- | ---: | ---: | ---: | ---: | ---: |
| Decoder allocation, ten registers | 4,064 | 163,840 | 2,710 | 313 | **308** |
| Packed counter, nine registers | 4,038 | 163,840 | 2,824 | 317 | 313 |
| Total | **8,102** | **327,680** | 5,534 | | |

Each run starts with 1,024 allocation plans, of which 984 distinct emitted-plan
and source-setting combinations are evaluated. It then retains 80 sources over
40 generations of 192 mutation attempts. Mutations vary allocations, field order,
clears and transfers together with the existing source/layout/factoring choices.
Every source evaluation includes the full reduction pipeline.

Sixteen diverse source finalists per run each receive 80 generations of 128 tree
mutation attempts, retaining up to 40 trees. Tree search screens by exact raw
count, fully reduces its leading candidates and final frontier, and audits every
accepted improvement against its source CFG. Closed fragments from the pinned
310-state tree are reused only when their register control flow matches. A raw
screen remains a heuristic; these results are not optimality bounds.

The two runs use one process each and a cooperative 512 MiB memory budget. Peak
RSS was 261 MiB and 277 MiB. Counts include repeats and exclude small probes,
smoke runs, artifact saves and verification. Recipes, winners and aggregate
results are in [the manifest](../reference/decoder-experiments.json); logs and
frontiers are not repository artifacts.

## Checking and reproducing

```sh
python3 tools/verify_ics.py
python3 -m unittest discover -s tests
python3 tools/check_decoder.py
python3 tools/experiment.py decoder-allocation
python3 tools/experiment.py decoder-packed-counter
```

The current candidate passes exact table/hash reproduction, 6,268 existing local
arithmetic/differential cases, 1,000 decoder/enumerator boundary cases, complete
factoring and final-tree CFG audits, and a CFG comparison of the unchanged
inference body. Literal simulation covers one million tape steps, plus comparison
of all ten registers at 512 decrement boundaries against the candidate's pre-tree
source. It does not compare the same numeric proof code against the old decoder.

The separate allocation sweep audited all 1,024 grid plans symbolically and ran
4,800 numerical boundary cases across 32 sampled plans and the three storage
modes. The packed-counter winner also passed 1,000 boundary cases and its tree
passed the full CFG audit; it was not promoted or subjected to the full literal
candidate verifier. The regression suite includes corrupt-plan
rejection, proof-field coding, stale-tree rejection and preserving a saved tree
when restarting search. The [Lean implementation proof](../formal/README.md) now verifies the incumbent’s
decoder and complete literal-tape execution; [verification scope](VERIFICATION.md)
distinguishes that result from the remaining theory interpretation.

To continue from the current candidate:

```sh
python3 tools/search_decoder.py --generations 40 --tree-generations 80 --tree-candidates 16
python3 tools/search_decoder.py --initial scratch/decoder.json \
  --resume-frontier scratch/decoder.frontier.json
python3 tools/search_tree.py --stratified --edge-rewrites
```

A resumed decoder search rebuilds sources and audits and scores saved trees before
selecting survivors. Historical joint/grammar/combined searches reject decoder
records, so they cannot silently replace this decoder with the old one. Use their
recorded replay recipes for comparisons with their original inputs.
