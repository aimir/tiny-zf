"""All-tape local contractions and exact transition congruence.

Algorithms adapted from this workspace's Riemann tools at commit c05cef7.
A finite-window reachability experiment is included; it is not a correctness
proof of the upstream compiler or of the ZF axiom system.
"""
from collections import deque


def quotient(rows):
    blocks = {q: 0 for q in rows}
    while True:
        classes, refined = {}, {}
        for q, row in rows.items():
            signature = tuple((w, d, blocks.get(t, -1)) for w, d, t in row)
            refined[q] = classes.setdefault(signature, len(classes))
        if refined == blocks:
            break
        blocks = refined
    representatives = {}
    for q in ['!ENTRY', *rows]:
        representatives.setdefault(blocks[q], q)
    mapping = {q: representatives[blocks[q]] for q in rows} | {'HALT': 'HALT'}
    result = {q: tuple((w, d, mapping[t]) for w, d, t in rows[q])
              for q in representatives.values()}
    check_quotient(rows, result, mapping)
    return result, mapping


def check_quotient(source, target, mapping):
    """Check every edge, not just sampled executions, of a proposed quotient."""
    if mapping.get('HALT') != 'HALT' or mapping.get('!ENTRY') != '!ENTRY':
        raise ValueError('quotient changes entry or halt')
    if set(mapping) != set(source) | {'HALT'} or set(target) != {mapping[q] for q in source}:
        raise ValueError('quotient coverage mismatch')
    for q, row in source.items():
        for bit, (w, d, t) in enumerate(row):
            if tuple(target[mapping[q]][bit]) != (w, d, mapping[t]):
                raise ValueError('quotient transition mismatch')


def local_macro(rows, state, read, length):
    """Enumerate every encountered initial tape bit, requiring identical outcomes."""
    paths = [(state, 0, {0: read}, {})]
    for step in range(length):
        following = []
        for q, head, initial, written in paths:
            if q == 'HALT':
                return None
            bits = ([written[head]] if head in written else
                    [initial[head]] if head in initial else (0, 1))
            for bit in bits:
                origin = initial.copy()
                origin.setdefault(head, bit)
                changed = written.copy()
                w, d, t = rows[q][bit]
                changed[head] = w
                newhead = head + d
                if abs(newhead) > length - step:
                    return None
                following.append((t, newhead, origin, changed))
        paths = following
    outcomes = set()
    for q, head, initial, written in paths:
        if head not in (-1, 1) or any(p != 0 and v != initial[p] for p, v in written.items()):
            return None
        outcomes.add((written.get(0, read), head, q))
    return next(iter(outcomes)) if len(outcomes) == 1 else None


def reachable(rows):
    seen, todo = set(), ['!ENTRY']
    while todo:
        q = todo.pop()
        if q == 'HALT' or q in seen:
            continue
        seen.add(q)
        todo.extend(t for _, _, t in rows[q])
    return {q: row for q, row in rows.items() if q in seen}


def reduce(rows):
    """Score the final table, including exact quotienting even without a macro."""
    rows, _ = quotient(reachable(rows))
    for _ in range(12):
        rewritten = {q: list(row) for q, row in rows.items()}
        for q, row in rows.items():
            for bit in (0, 1):
                for length in (3, 5, 7):
                    edge = local_macro(rows, q, bit, length)
                    if edge is not None and edge != tuple(row[bit]):
                        rewritten[q][bit] = edge
                        break
        result, _ = quotient(reachable(rewritten))
        if len(result) >= len(rows):
            break
        rows = result
    return rows


def window_reads(rows, left, right, allowed=None):
    """Sound blank-tape overapproximation: unseen boundary bits are arbitrary."""
    names = list(rows)
    index = {q: i for i, q in enumerate(names)}
    bits = left + right + 1
    mask, center = (1 << bits) - 1, 1 << left
    edges = [[(w, d, index.get(t, -1)) for w, d, t in rows[q]] for q in names]
    masks = [allowed[q] if allowed is not None else 3 for q in names]
    start = index['!ENTRY'] << bits
    todo, seen, possible = deque([start]), {start}, [0] * len(names)
    while todo:
        config = todo.popleft()
        q, window = config >> bits, config & mask
        bit = (window >> left) & 1
        if not masks[q] & (1 << bit):
            continue
        possible[q] |= 1 << bit
        w, d, t = edges[q][bit]
        if t < 0:
            continue
        window = (window & ~center) | (w << left)
        if d == 1:
            a = (t << bits) | (window >> 1)
            b = a | (1 << (bits - 1))
        else:
            a = (t << bits) | ((window << 1) & mask)
            b = a | 1
        for successor in (a, b):
            if successor not in seen:
                seen.add(successor)
                todo.append(successor)
    return dict(zip(names, possible)), len(seen)
