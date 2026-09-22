"""Bounded, deterministic beam search scored after the complete local reduction.

The retained frontier permits sideways moves. Workers only compile candidates;
all search choices and tie-breaking happen in the parent with a fixed seed.
"""
import argparse
import json
import multiprocessing as mp
from pathlib import Path
import random
import time
from machines import ROOT, UPSTREAM_ORDER, DISTINCT_ORDER, build, count, totalize, write_table
from reduce import reduce


def score(order):
    machine = build(order)
    rows = totalize(machine.tm.start, machine.tm.states)
    return len(reduce(rows)), count(machine.tm.states), tuple(order)


def mutate(order, rng):
    result = list(order)
    n = len(result)
    kind = rng.randrange(5)
    if kind == 0:
        a, b = rng.sample(range(n), 2)
        result[a], result[b] = result[b], result[a]
    elif kind == 1:
        a, b = rng.sample(range(n), 2)
        result.insert(b, result.pop(a))
    elif kind == 2:
        a, b, c = sorted(rng.sample(range(n + 1), 3))
        result = result[:a] + result[b:c] + result[a:b] + result[c:]
    elif kind == 3:
        a, b = sorted(rng.sample(range(n), 2))
        result[a:b + 1] = reversed(result[a:b + 1])
    else:
        for _ in range(rng.randrange(2, 5)):
            a, b = rng.sample(range(n), 2)
            result[a], result[b] = result[b], result[a]
    return tuple(result)


def search(args):
    initial = DISTINCT_ORDER if args.distinct else UPSTREAM_ORDER
    if args.initial:
        initial = tuple(json.loads(args.initial.read_text())['order'])
    beam = [score(initial)]
    champion = beam[0]
    seen = {initial}
    rng = random.Random(args.seed)
    history = []
    start = time.monotonic()
    with mp.Pool(args.workers) as pool:
        for generation in range(args.generations):
            batch = set()
            while len(batch) < args.batch:
                parent = rng.choice(beam)[2]
                candidate = mutate(parent, rng)
                if candidate[-1] not in (0, 1) and candidate not in seen:
                    batch.add(candidate)
            seen.update(batch)
            results = pool.map(score, sorted(batch))
            union = beam + results
            rng.shuffle(union)
            union.sort(key=lambda result: result[0])
            beam = union[:args.width]
            if beam[0][0] < champion[0]:
                champion = beam[0]
                history.append({'generation': generation, 'final_states': champion[0],
                                'raw_states': champion[1], 'order': champion[2],
                                'evaluations': len(seen)})
            print(f'generation {generation + 1}: best {champion[0]}, '
                  f'frontier {beam[0][0]}..{beam[-1][0]}, {len(seen)} evaluations', flush=True)
    report = {'seed': args.seed, 'generations': args.generations, 'batch': args.batch,
              'width': args.width, 'workers': args.workers, 'distinct': args.distinct,
              'initial_order': initial, 'evaluations': len(seen),
              'final_states': champion[0], 'raw_states': champion[1], 'order': champion[2],
              'improvements': history, 'seconds': round(time.monotonic() - start, 3)}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + '\n')
    write_table(args.output.with_suffix('.tm'), build(champion[2]))
    # The emitted .tm is the RAW compiler output; metadata gives both counts.
    # Promotions must independently rebuild and check the complete result.
    print(json.dumps(report, indent=2))


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--distinct', action='store_true', help='remove the duplicate B6b/B8b copies')
    p.add_argument('--initial', type=Path, help='start from an earlier result JSON')
    p.add_argument('--seed', type=int, default=20260922)
    p.add_argument('--generations', type=int, default=40)
    p.add_argument('--batch', type=int, default=160)
    p.add_argument('--width', type=int, default=64)
    p.add_argument('--workers', type=int, default=4)
    p.add_argument('--output', type=Path, default=ROOT / 'scratch' / 'search.json')
    args = p.parse_args()
    if min(args.generations, args.batch, args.width, args.workers) < 1:
        p.error('search dimensions must be positive')
    search(args)


if __name__ == '__main__':
    main()
