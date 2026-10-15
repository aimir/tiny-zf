"""Reproduce the Coq-verified 251-, 252- and 253-state native machines.

The pinned 254-state machine supplies the decoder and source program. This
construction changes the positive-decrement loop and optionally removes the
dedicated bootstrap state, then densely renumbers the literal table. The Coq acceptance
driver proves the unbounded kernel contract and the complete ZF/ZFC endpoint.
"""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path

from compare_mira254 import checked_inputs, recover


def acceptance_module():
    path = Path(__file__).resolve().parents[1] / 'formal/coq/candidate.py'
    spec = importlib.util.spec_from_file_location('mira_forward_acceptance', path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def build(checkout, mode='forward'):
    """Return the canonical literal table and unchanged, validated decoder tree."""
    directory = checked_inputs(checkout)
    acceptance = acceptance_module()
    rows = acceptance.parse_table((directory / 'machine/zfc_254.tm').read_text())
    # Carry the deleted cell forward across register blocks, ending with the
    # same appended zero register as the original reverse-shifting algorithm.
    rows.update({
        ('75', 1): (1, 'L', '112'),
        ('112', 0): (1, 'R', '97'),
        ('112', 1): (0, 'R', '112'),
        ('97', 0): (0, 'L', '63'),
        ('85', 0): (0, 'L', '112'),
    })
    rows = {(q, b): (w, d, '112' if target == '131' else target)
            for (q, b), (w, d, target) in rows.items() if q != '131'}
    if mode in ('local', 'startup'):
        # Swap the gap past one cell at a time. This needs two states instead
        # of a separate run scanner, end test and gap state.
        rows.update({('112', 0): (1, 'R', '85'), ('112', 1): (1, 'L', '112'),
                     ('85', 0): (0, 'L', '63'), ('85', 1): (0, 'R', '112')})
        rows = {key: edge for key, edge in rows.items() if key[0] != '97'}
        anchors = acceptance.LOCAL_ANCHORS
        if mode == 'startup':
            # The shared mark-return path and increment detour permit startup
            # without state 8. The machine reaches the third enumerator state:
            # nextproof=3, param1=1, other active registers zero, PC gap 40.
            rows.update({('0', 1): (0, 'L', '4'),
                         ('5', 1): (0, 'L', '5'),
                         ('109', 0): (0, 'R', '85')})
            rows = {key: edge for key, edge in rows.items() if key[0] != '8'}
            anchors = acceptance.STARTUP_ANCHORS
    elif mode == 'forward':
        anchors = acceptance.FORWARD_ANCHORS
    else:
        raise ValueError('unknown decrement implementation')
    canonical, _ = acceptance.canonicalize(rows, anchors=anchors)
    tree, root, _ = recover((directory / 'coq/tm/Prog254.v').read_text(), True)
    return acceptance.table_text(canonical), tree.export(root)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--upstream', required=True, type=Path)
    parser.add_argument('--output', required=True, type=Path)
    parser.add_argument('--mode', choices=('forward', 'local', 'startup'), default='startup',
                        help='251-state startup, 252-state local gap carry or 253-state block stream')
    args = parser.parse_args()
    table, tree = build(args.upstream, args.mode)
    size = {'startup': 251, 'local': 252, 'forward': 253}[args.mode]
    tree_text = json.dumps(tree, indent=2) + '\n'
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(table)
    args.output.with_suffix('.tree.json').write_text(tree_text)
    print(json.dumps({
        'working_states': size,
        'terminal': size,
        'machine_sha256': hashlib.sha256(table.encode()).hexdigest(),
        'instruction_tree_sha256': hashlib.sha256(tree_text.encode()).hexdigest(),
        'formal_verification': 'Run formal/coq/candidate.py with --halt '
                               + str(size)
                               + ' --decrement-mode ' + args.mode,
    }, indent=2))


if __name__ == '__main__':
    main()
