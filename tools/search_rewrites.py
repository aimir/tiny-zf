"""Joint beam over protected-formula rewrites, source layout and factoring seed.

All five protected formulas may use their original syntax (choice -1) or an
NNF expression. The twelve logical/inference clauses are never rewritten.
Scores include the complete local contraction and state-quotient pipeline.
"""
import argparse
from functools import partial
import json
import multiprocessing as mp
from pathlib import Path
import random

from formula_rewrite import LIMITS, check_choices
from ics import RPN
from joint import build_joint, decode, encode
from machines import ROOT, count, write_table, totalize
from reduce import reduce
from search_joint import mutation

NAMES = tuple(RPN)


def formula_choices(choices):
    return {name: value for name, value in zip(NAMES, choices) if value >= 0}


def evaluate(gene, grammar):
    config, choices, seed = gene
    m = build_joint(config, sharing=True, grammar={**grammar, 'seed': seed},
                    formula_choices=formula_choices(choices))
    return len(reduce(totalize(m.tm.start, m.tm.states))), count(m.tm.states), gene


def mutate(gene, rng):
    config, choices, seed = gene
    kind = rng.randrange(10)
    if kind < 5:
        choices = list(choices)
        for _ in range(1 if kind < 4 else 3):
            j = rng.randrange(len(NAMES))
            choices[j] = rng.randrange(-1, LIMITS[NAMES[j]])
        choices = tuple(choices)
    elif kind < 9:
        config = mutation(config, rng)
    else:
        seed = rng.randrange(2**24)
    return config, choices, seed


def run(args):
    record = json.loads(args.initial.read_text())
    if record.get('decoder'):raise ValueError('decoder allocation present: use search_decoder.py to preserve it')
    if record.get("instruction_tree"):
        print("Source search rebuilds the saved source; run search_tree.py on its output to optimize the changed tree.",flush=True)
    if not record.get('shared_operations') or not record.get('two_scratch'):
        raise ValueError('rewrite search requires the shared two-scratch source')
    grammar = record['grammar']
    initial = (decode(record), tuple(record.get('formula_choices', {}).get(n, -1)
                                    for n in NAMES), grammar['seed'])
    score = partial(evaluate, grammar=grammar)
    best = score(initial)
    beam = [best]
    seen = {initial}
    rng = random.Random(args.seed)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    with mp.Pool(args.workers) as pool:
        for generation in range(args.generations):
            batch = set()
            while len(batch) < args.batch:
                gene = mutate(rng.choice(beam)[2], rng)
                if gene not in seen:
                    batch.add(gene)
            seen.update(batch)
            union = beam + pool.map(score, sorted(batch))
            rng.shuffle(union)
            union.sort(key=lambda row: row[0])
            beam = union[:args.width]
            if beam[0][0] < best[0]:
                best = beam[0]
            config, choices, seed = best[2]
            report = {'kind': 'ics-formula-rewrites', 'seed': args.seed,
                      'generations': generation + 1, 'width': args.width,
                      'batch': args.batch, 'evaluations': len(seen),
                      'raw_states': best[1], 'final_states': best[0],
                      'formula_choices': formula_choices(choices),
                      **encode(config), 'grammar': {**grammar, 'seed': seed},
                      'shared_operations': True}
            args.output.write_text(json.dumps(report, indent=2) + '\n')
            print(f'generation {generation + 1}: {best[0]}, '
                  f'frontier {beam[0][0]}..{beam[-1][0]}, {len(seen)} evaluated',
                  flush=True)
    check_choices(report['formula_choices'])
    m = build_joint(config, sharing=True, grammar=report['grammar'],
                    formula_choices=report['formula_choices'])
    write_table(args.output.with_suffix('.tm'), m)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--initial', type=Path, default=ROOT/'candidates/ics-best.json')
    parser.add_argument('--seed', type=int, default=20261002)
    parser.add_argument('--width', type=int, default=128)
    parser.add_argument('--batch', type=int, default=256)
    parser.add_argument('--generations', type=int, default=80)
    parser.add_argument('--workers', type=int, default=4)
    parser.add_argument('--output', type=Path, default=ROOT/'scratch/ics-rewrites.json')
    args = parser.parse_args()
    if min(args.width, args.batch, args.generations, args.workers) < 1:
        parser.error('search sizes and worker count must be positive')
    run(args)
