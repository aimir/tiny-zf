"""Reproduction and bounded checks, explicitly NOT a formal ZF proof."""
import argparse
from functools import lru_cache
import hashlib
import json
from machines import (ROOT, ALIASES, build, count, read_table, require, totalize, validate_order)
from reduce import reduce, window_reads


def fingerprints(machine):
    """Compare structured source clauses independently of sequence-node numbering."""
    clauses = machine.axioms()

    @lru_cache(None)
    def node(index):
        return tuple(expand(x) for x in machine.sequences[index].seq)

    def expand(x):
        if isinstance(x, int):
            return node(x)
        if isinstance(x, (list, tuple)):
            return tuple(expand(y) for y in x)
        return x

    return [expand(clause) for clause in clauses]


def simulate(start, edges, steps):
    """Independent literal two-way-tape simulator; only a bounded smoke check."""
    ones, head, q, dispatches = set(), 0, start, 0
    for step in range(steps):
        if q == 'main().0':
            dispatches += 1
        edge = edges.get((q, str(int(head in ones))))
        require(edge is not None, f'unexpected halt in finite smoke check at step {step}: {q}')
        w, d, q = edge
        if w == '1':
            ones.add(head)
        else:
            ones.discard(head)
        head += 1 if d == 'R' else -1
    return {'steps': steps, 'dispatches': dispatches, 'state': q, 'head': head,
            'ones': len(ones), 'span': max(ones) - min(ones) + 1 if ones else 0}


def verify(steps=1_000_000, windows=False):
    manifest = json.loads((ROOT / 'reference' / 'upstream.json').read_text())
    for relative, digest in manifest['files_sha256'].items():
        require(hashlib.sha256((ROOT / 'vendor' / 'wade' / relative).read_bytes()).hexdigest() == digest,
                f'upstream snapshot changed: {relative}')
    upstream = build()
    start, saved = read_table(ROOT / 'vendor' / 'wade' / 'zf2.tm')
    require(start == upstream.tm.start and saved == upstream.tm.states,
            'upstream compilation does not match pinned table exactly')
    require(count(saved) == manifest['states'] == 393, 'upstream state count changed')
    require(sum(q[0].isdigit() for q in {q for q, b in saved}) == 69, 'framework count changed')
    symbols = {q for q, b in saved}
    require({(q, b) for q in symbols for b in ('0', '1') if (q, b) not in saved} == {('1.inc', '1')},
            'partial-transition convention changed')
    clauses = fingerprints(type(upstream)())
    for duplicate, retained in ALIASES.items():
        require(clauses[duplicate] == clauses[retained], 'alleged duplicate clauses differ')
    result = json.loads((ROOT / 'candidates' / 'best.json').read_text())
    validate_order(result['order'])
    # Set comparison retains every distinct inference/axiom implementation.
    require(set(clauses) == {clauses[i] for i in result['order']}, 'clause coverage changed')
    candidate = build(result['order'])
    candidate_start, candidate_saved = read_table(ROOT / 'candidates' / 'best.tm')
    require(candidate_start == candidate.tm.start and candidate_saved == candidate.tm.states,
            'candidate compilation does not match saved table exactly')
    require(count(candidate_saved) == result['raw_states'], 'candidate raw count mismatch')
    final = reduce(totalize(candidate_start, candidate_saved))
    require(len(final) == result['final_states'], 'candidate final count mismatch')
    # This initial candidate needs no table-level rewrite; the partial source table
    # is the literal advertised machine, with no hidden reduction certificates.
    require(len(final) == count(candidate_saved), 'save and verify a reduction certificate before promotion')
    report = {'status': 'reproduced; not formally verified', 'upstream_states': count(saved),
              'candidate_states': len(final), 'distinct_source_clauses': len(set(clauses)),
              'upstream_smoke': simulate(start, saved, steps),
              'candidate_smoke': simulate(candidate_start, candidate_saved, steps)}
    if windows:
        rows = totalize(start, saved)
        allowed = {q: 3 for q in rows}
        report['upstream_windows'] = []
        for left, right in ((3, 3), (8, 2), (2, 8), (5, 5), (10, 2), (2, 10), (6, 6)):
            possible, configs = window_reads(rows, left, right, allowed)
            allowed = {q: allowed[q] & possible[q] for q in rows}
            report['upstream_windows'].append({'left': left, 'right': right, 'configurations': configs,
                                               'allowed_state_reads': sum(x.bit_count() for x in allowed.values())})
    return report


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--steps', type=int, default=1_000_000)
    p.add_argument('--windows', action='store_true', help='also repeat the larger reachability experiment')
    args = p.parse_args()
    require(args.steps >= 0, 'steps must be nonnegative')
    print(json.dumps(verify(args.steps, args.windows), indent=2))
