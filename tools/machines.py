"""Pinned upstream compiler, strict blank-tape table reader, and state counting."""
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'vendor' / 'wade'))
from zf2 import ZF2  # noqa: E402

UPSTREAM_ORDER = (16, 17, 3, 18, 4, 7, 8, 9, 11, 5, 12, 13, 14, 2, 15, 0, 1, 6, 10, 19)
DISTINCT_ORDER = tuple(i for i in UPSTREAM_ORDER if i not in (6, 7))
# Keep either copy of each of these byte-for-byte identical clauses.
ALIASES = {6: 9, 7: 13}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def validate_order(order):
    """Check coverage, no introduced clauses, and the upstream cparam restriction."""
    require(bool(order), 'empty axiom order')
    require(all(type(i) is int and 0 <= i < 20 for i in order), 'invalid clause index')
    require(len(set(order)) == len(order), 'repeated clause index')
    require(order[-1] not in (0, 1), 'DET/GEN must not be last')
    require({ALIASES.get(i, i) for i in order} == {ALIASES.get(i, i) for i in range(20)},
            'missing axiom/inference clause')


def build(order=UPSTREAM_ORDER):
    validate_order(order)
    machine = ZF2()
    machine.debug = False
    machine.AXIOMORDER = list(order)
    machine.build_machine()
    return machine


def count(states):
    return len({q for q, bit in states})


def read_table(path):
    """Read only binary L/R tables on a blank tape; reject silent initialization."""
    start = None
    edges = {}
    for number, line in enumerate(Path(path).read_text().splitlines(), 1):
        line = line.strip()
        if not line:
            continue
        if line.startswith('#!'):
            fields = line.split()
            if fields[:2] == ['#!', 'start'] and len(fields) == 3:
                require(start is None, 'duplicate start directive')
                start = fields[2]
            elif fields == ['#!', 'fill', '0']:
                pass
            else:
                raise ValueError(f'unsupported tape directive at line {number}: {line}')
        elif not line.startswith('#'):
            fields = line.split()
            require(len(fields) == 5, f'bad transition at line {number}')
            q, bit, write, move, target = fields
            require(bit in ('0', '1') and write in ('0', '1') and move in ('L', 'R'),
                    f'not binary L/R at line {number}')
            require((q, bit) not in edges, f'duplicate transition at line {number}')
            edges[q, bit] = (write, move, target)
    names = {q for q, bit in edges}
    require(start in names, 'missing or invalid start state')
    require(all(target in names or target == 'halt' for _, _, target in edges.values()),
            'unexpected undefined target')
    return start, edges


def totalize(start, edges):
    """Canonical complete rows. Missing reads take one extra step to HALT.

    This preserves existence of halting, not the exact time or terminal tape
    of an undefined transition. All explicit transitions are preserved.
    """
    names = {q for q, bit in edges}
    rename = lambda q: '!ENTRY' if q == start else 'HALT' if q == 'halt' else q
    require('!ENTRY' not in names and 'HALT' not in names, 'reserved state name')
    require(all(target in names or target == 'halt' for _, _, target in edges.values()),
            'unexpected undefined target')
    return {rename(q): tuple((int(w), 1 if d == 'R' else -1, rename(t))
                            for w, d, t in (edges.get((q, str(b)), (str(b), 'R', 'halt'))
                                            for b in (0, 1)))
            for q in sorted(names)}


def write_table(path, machine):
    lines = [f'#! start {machine.tm.start}']
    lines += [' '.join((q, b, *e)) for (q, b), e in sorted(machine.tm.states.items())]
    Path(path).write_text('\n'.join(lines) + '\n')
