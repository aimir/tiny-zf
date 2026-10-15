"""Reconstruct and compare Mira-Cult's checked programs without its missing source bundle.

The input is a pinned checkout of jeff87654/busy-beaver. The Coq definitions
are data inputs; our existing compiler and CFG checker evaluate the recovered
trees. Counts from Wade's backend are NOT counts for the 254-state backend.
"""
import argparse
import ast
from functools import lru_cache
import hashlib
import json
from pathlib import Path
import random
import re
import subprocess
import sys
import tempfile

from machines import ROOT, count, read_table, totalize
from instruction_tree import Trees
from reduce import reduce, reachable, window_reads
from register_check import compile_fragment
from verify_tree import equivalent_increment_cfg
from TMBuilder import TMBuilder

COMMIT = '297ab8df7e5de329605c3875b4934643b371a5e3'
HASHES = {
    'machine/zfc_254.tm': 'd655ce2cf8cccebd21caa21a49f0f9f010960a44b95c17aae6cc425c518954eb',
    'coq/tm/Prog254.v': '1fbc30fcf82a1442ed88d1a1dde412630a431d32a7265d22bdf8517bffe01746',
    'coq/prog/Dag254.v': '538ddaddd932058c2b319011126579d77783231f54331772377c05848a0599e3',
    'tools/tm/symexec.py': '5bf83da419c47b9c8d79fcc755e40048f599255c2f1b2cb4656dc04bb02bb85d',
    'tools/tm/tmlib.py': 'd66c407bfa9e78b01a3cd1f363beb3d68d6091eabc007caabc915ff972b4ca00',
}
REGISTERS = ('nextproof', 'topwff', 'wffstack', 'axiomcode', 'param1',
             'param2', 'scratch1', 'scratch2', 'prooflist')


def checked_inputs(checkout):
    """Reject a changed machine, program definition, or external checker."""
    directory = checkout / 'ZF/m254'
    for relative, digest in HASHES.items():
        if hashlib.sha256((directory / relative).read_bytes()).hexdigest() != digest:
            raise ValueError(f'upstream input hash mismatch: {relative}')
    return directory


def recover(text, optimized):
    """Read literal Coq edges, then validate bounds, acyclicity and op kinds."""
    if optimized:
        pairs = re.findall(r'\((C[NIDBC] \d+|CH), (C[NIDBC] \d+|CH)\)', text)
        nodes = dict(enumerate(pairs))
        kinds = dict(CN='node', CI='inc', CD='decnz', CB='break', CC='continue', CH='halt')
    else:
        pairs = re.findall(r'\| (\d+) => \((E\w+(?: \d+)?), (E\w+(?: \d+)?)\)', text)
        nodes = {int(i): (a, b) for i, a, b in pairs}
        if len(nodes) != len(pairs):
            raise ValueError('duplicate Coq node')
        kinds = dict(ENode='node', EInc='inc', EDecnz='decnz',
                     EBreak='break', EContinue='continue', EHalt='halt')
    if not nodes or set(nodes) != set(range(len(nodes))):
        raise ValueError('Coq nodes must be contiguous and include root zero')
    tree = Trees()
    active = set()

    @lru_cache(None)
    def visit_node(n):
        if n not in nodes or n in active:
            raise ValueError('missing or cyclic Coq node')
        active.add(n)
        result = tree.node(*(edge(e) for e in nodes[n]))
        active.remove(n)
        return result

    def edge(value):
        fields = value.split()
        kind = kinds.get(fields[0])
        if kind is None or len(fields) != (1 if kind == 'halt' else 2):
            raise ValueError('unknown Coq edge')
        if kind == 'halt':
            return 'halt'
        n = int(fields[1])
        if n < 0:
            raise ValueError('negative operand')
        if kind == 'node':
            return visit_node(n)
        if kind in ('inc', 'decnz'):
            if n >= len(REGISTERS):
                raise ValueError('invalid register index')
            return f'3.{REGISTERS[n]}.{kind}'
        return f'_{kind}.{n}'

    root = visit_node(0)
    return tree, root, len(nodes)


def compile_tree(tree, root):
    machine = TMBuilder()
    for register in REGISTERS:
        machine.reg(register)
    tree.install(machine, root)
    machine.name_sequences()
    machine.generate()
    machine.tm.gc()
    return machine


def cfg(tree, root):
    machine = compile_tree(tree, root)
    return compile_fragment(machine, machine.find_seq('main().0'), terminal='return')


def score(tree, root):
    machine = compile_tree(tree, root)
    return len(reduce(totalize(machine.tm.start, machine.tm.states)))


def normalized_table(directory):
    """Only rename the explicitly known undefined target 254 to our HALT spelling."""
    lines = []
    for line in (directory / 'machine/zfc_254.tm').read_text().splitlines():
        fields = line.split()
        if not line.startswith('#') and len(fields) == 5 and fields[-1] == '254':
            fields[-1] = 'halt'
            line = ' '.join(fields)
        lines.append(line)
    with tempfile.TemporaryDirectory() as temporary:
        path = Path(temporary) / 'table.tm'
        path.write_text('\n'.join(lines) + '\n')
        start, edges = read_table(path)
    if count(edges) != 254:
        raise ValueError('wrong machine size')
    return start, edges


def paths(tree, root):
    result = []
    def walk(v, prefix):
        if isinstance(v, str):
            result.append(['110' + prefix, v])
        else:
            for bit, child in enumerate(tree.nodes[v]):
                walk(child, prefix + str(bit))
    walk(root, '')
    return result


def symbolic_check(directory, table, tree, root):
    """Run the pinned Python model, rejecting reported failures even with exit 0.

    This checks every symbolic instruction site, not the bootstrap or box
    lemmas, and is NOT a replacement for rebuilding the upstream Coq proof.
    """
    with tempfile.TemporaryDirectory() as temporary:
        folder = Path(temporary)
        (folder / 'paths.json').write_text(json.dumps(paths(tree, root)))
        result = subprocess.run(
            [sys.executable, str(directory / 'tools/tm/symexec.py'),
             str(table.resolve()), str(folder), '40'],
            capture_output=True, text=True, timeout=180)
    matches = re.findall(r'^D0 = 40 (\{.*?\}) (\{.*\})$', result.stdout, re.M)
    counts = ast.literal_eval(matches[-1][0]) if matches else {}
    expected_cases = sum(2 if op.endswith('.decnz') else 1 for _, op in paths(tree, root))
    passed = (result.returncode == 0 and bool(counts) and
              set(counts) <= {'ok normal', 'ok overflow', 'halt'} and
              counts.get('halt') == 1 and sum(counts.values()) == expected_cases)
    return {'passed': passed, 'cases': expected_cases, 'outcomes': counts,
            'returncode': result.returncode}


def rejected_graft(directory, tree, root):
    """Replay the attractive 253-state transplant and its tape-level rejection.

    Node IDs refer only to the hash-pinned recovered program. This deliberately
    invalid table is kept in a temporary directory and never emitted as a candidate.
    """
    if tree.nodes[74] != (39, 73) or tree.nodes[73] != (47, 63):
        raise ValueError('unexpected pinned-tree numbering')
    replacement = tree.node(48, 63)
    if replacement not in tree.rotations(74):
        raise ValueError('expected register-program rotation unavailable')
    changed = tree.replace(root, 74, replacement)
    pairs = equivalent_increment_cfg(cfg(tree, root), cfg(tree, changed))
    start, edges = normalized_table(directory)
    edges['178', '0'] = ('0', 'R', '16')
    edges['178', '1'] = ('1', 'R', '206')
    rows = reachable(totalize(start, edges))
    with tempfile.TemporaryDirectory() as temporary:
        path = Path(temporary) / 'invalid-graft.tm'
        lines = [f'#! start {start}']
        for (q, bit), (w, d, target) in sorted(edges.items()):
            if q == start or q in rows:
                lines.append(' '.join((q, bit, w, d, '254' if target == 'halt' else target)))
        path.write_text('\n'.join(lines) + '\n')
        result = symbolic_check(directory, path, tree, changed)
    return {'proposed_states': len(rows), 'matched_register_segments': pairs,
            'tape_check': result, 'accepted': False,
            'instruction_counterexample': concrete_graft_check(edges, paths(tree, changed)),
            'reason': 'shared tape states depend on PC contexts changed by the transplant'}


def concrete_graft_check(edges, program_paths):
    """A literal finite counterexample to the graft's instruction contract.

    All twenty physical registers are zero, so this decrement must take its
    zero branch. This is an instruction-boundary fixture, not blank tape.
    """
    word, op = program_paths[894]
    if op != '3.topwff.decnz':
        raise ValueError('unexpected counterexample site')
    word = word[3:]
    stripped = word[:word.rindex('0')]
    expected = stripped[:stripped.rindex('0')] + '1'
    gap = 62
    tape = {-1, gap} | {i for i, b in enumerate(word) if b == '1'}
    tape |= {gap + 2 + 2 * i for i in range(20)}
    q, head = '96', 0
    for steps in range(1, 10001):
        edge = edges.get((q, str(int(head in tape))))
        if edge is None:
            raise ValueError('counterexample halted unexpectedly')
        w, d, q = edge
        if w == '1':
            tape.add(head)
        else:
            tape.discard(head)
        head += 1 if d == 'R' else -1
        if (q == '96' and head == 0 and -1 in tape and gap in tape and
                not any(i in tape for i in range(35, gap))):
            actual = ''.join(str(int(i in tape)) for i in range(gap)).rstrip('0')
            if actual == expected:
                raise ValueError('counterexample no longer demonstrates a mismatch')
            return {'site': 894, 'operation': op, 'initial_pc': word,
                    'initial_register_values': [0] * 20, 'marker_to_header_gap': gap,
                    'steps': steps, 'expected_pc': expected, 'actual_pc': actual,
                    'scope': 'instruction contract; not a blank-tape counterexample'}
    raise ValueError('counterexample did not return to dispatch')


def beam(tree, root, args):
    """Screen several trees; fully reduce leaders and the whole final frontier."""
    original = cfg(tree, root)
    rng = random.Random(args.seed)
    frontier = [root]
    best, best_score = root, score(tree, root)
    fixed = count(compile_tree(tree, root).tm.states) - tree.size(root)
    evaluated = 0
    for generation in range(args.generations):
        trial = set(frontier)
        for _ in range(args.batch):
            current = rng.choice(frontier)
            for _ in range(1 if rng.randrange(4) else 2):
                options = [(v, w) for v in tree.reachable(current) for w in tree.rotations(v)]
                if not options:
                    break
                v, w = rng.choice(options)
                current = tree.replace(current, v, w)
            trial.add(current)
        ranked = [(tree.size(v) + fixed, v) for v in trial]
        rng.shuffle(ranked)
        ranked.sort(key=lambda item: item[0])
        frontier = [v for _, v in ranked[:args.width]]
        for _, v in ranked[:3]:
            actual = score(tree, v)
            evaluated += 1
            if actual < best_score:
                equivalent_increment_cfg(original, cfg(tree, v))
                best, best_score = v, actual
        if (generation + 1) % 10 == 0:
            print(f'generation {generation + 1}: {best_score} states on Wade backend', flush=True)
        old = tree
        tree, roots = old.compact([best, *frontier])
        best, *frontier = roots
        old.clear_caches()
    for v in frontier:
        actual = score(tree, v)
        evaluated += 1
        if actual < best_score:
            best, best_score = v, actual
    pairs = equivalent_increment_cfg(original, cfg(tree, best))
    args.output.with_suffix('.tree.json').write_text(json.dumps(tree.export(best), indent=2) + '\n')
    return {'states_wade_backend': best_score, 'dag_nodes': len(tree.reachable(best)),
            'matched_segments': pairs, 'fully_reduced': evaluated,
            'seed': args.seed, 'generations': args.generations,
            'batch': args.batch, 'width': args.width}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--upstream', required=True, type=Path)
    parser.add_argument('--output', type=Path, default=ROOT / 'scratch/mira254.json')
    parser.add_argument('--verify-tree', type=Path)
    parser.add_argument('--symbolic-check', action='store_true')
    parser.add_argument('--probe-graft', action='store_true')
    parser.add_argument('--generations', type=int, default=0)
    parser.add_argument('--seed', type=int, default=25420261015)
    parser.add_argument('--width', type=int, default=64)
    parser.add_argument('--batch', type=int, default=256)
    args = parser.parse_args()
    if args.generations < 0 or min(args.width, args.batch) < 1:
        parser.error('invalid search dimensions')
    directory = checked_inputs(args.upstream.resolve())
    args.output.parent.mkdir(parents=True, exist_ok=True)
    source, a, _ = recover((directory / 'coq/prog/Dag254.v').read_text(), False)
    optimized, b, _ = recover((directory / 'coq/tm/Prog254.v').read_text(), True)
    rows = totalize(*normalized_table(directory))
    report = {'upstream_commit': COMMIT, 'input_sha256': HASHES,
              'source_wade_states': score(source, a),
              'optimized_wade_states': score(optimized, b),
              'upstream_states': len(rows), 'all_tape_reduced_states': len(reduce(rows))}
    report['windows'] = []
    allowed = {q: 3 for q in rows}
    for left, right in ((3, 3), (4, 4), (5, 5), (8, 2), (2, 8), (6, 6), (8, 8)):
        possible, explored = window_reads(rows, left, right, allowed)
        allowed = {q: allowed[q] & possible[q] for q in rows}
        report['windows'].append({'left': left, 'right': right, 'contexts': explored,
                                  'excluded_reads': sum(2 - v.bit_count() for v in allowed.values())})
    if args.symbolic_check:
        report['upstream_symbolic_check'] = symbolic_check(
            directory, directory / 'machine/zfc_254.tm', optimized, b)
        if not report['upstream_symbolic_check']['passed']:
            raise ValueError('upstream symbolic check failed')
    if args.verify_tree:
        candidate = Trees()
        c = candidate.import_record(json.loads(args.verify_tree.read_text()))
        report['retained_tree'] = {
            'sha256': hashlib.sha256(args.verify_tree.read_bytes()).hexdigest(),
            'states_wade_backend': score(candidate, c),
            'dag_nodes': len(candidate.reachable(c)),
            'matched_segments': equivalent_increment_cfg(cfg(optimized, b), cfg(candidate, c))}
    if args.probe_graft:
        report['rejected_graft'] = rejected_graft(directory, optimized, b)
        if report['rejected_graft']['tape_check']['passed']:
            raise ValueError('unexpected result: re-investigate graft before classifying it')
    if args.generations:
        report['beam'] = beam(optimized, b, args)
    args.output.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
