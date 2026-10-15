"""Reproduce the Coq-verified 252- and 253-state forward-decrement machines.

The pinned 254-state machine supplies the decoder and source program. This
construction changes the positive-decrement loop, shares its gap state, and
densely renumbers the resulting literal table. The separate Coq acceptance
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
    if mode == 'local':
        # Swap the gap past one cell at a time. This needs two states instead
        # of a separate run scanner, end test and gap state.
        rows.update({('112', 0): (1, 'R', '85'), ('112', 1): (1, 'L', '112'),
                     ('85', 0): (0, 'L', '63'), ('85', 1): (0, 'R', '112')})
        rows = {key: edge for key, edge in rows.items() if key[0] != '97'}
        anchors = acceptance.LOCAL_ANCHORS
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
    parser.add_argument('--mode', choices=('forward', 'local'), default='forward',
                        help='253-state block stream or 252-state local gap carry')
    args = parser.parse_args()
    table, tree = build(args.upstream, args.mode)
    tree_text = json.dumps(tree, indent=2) + '\n'
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(table)
    args.output.with_suffix('.tree.json').write_text(tree_text)
    print(json.dumps({
        'working_states': 252 if args.mode == 'local' else 253,
        'terminal': 252 if args.mode == 'local' else 253,
        'machine_sha256': hashlib.sha256(table.encode()).hexdigest(),
        'instruction_tree_sha256': hashlib.sha256(tree_text.encode()).hexdigest(),
        'formal_verification': 'Run formal/coq/candidate.py with --halt '
                               + ('252' if args.mode == 'local' else '253')
                               + ' --decrement-mode ' + args.mode,
    }, indent=2))


if __name__ == '__main__':
    main()
