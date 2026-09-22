"""Search ICS clause order within the required parameter-safety phases."""
import argparse
import json
import multiprocessing as mp
from pathlib import Path
import random
from machines import ROOT, count, totalize, write_table
from ics import LOGICAL, LABELS, build_ics
from reduce import reduce
from search import mutate


def score(order):
    machine = build_ics(order)
    return len(reduce(totalize(machine.tm.start, machine.tm.states))), count(machine.tm.states), order


def run(args):
    order = tuple(range(len(LABELS))) if args.initial is None else tuple(json.loads(args.initial.read_text())['order'])
    beam = [score(order)]
    champion = beam[0]
    initial_states = champion[0]
    seen = {order}
    rng = random.Random(args.seed)
    improvements = []
    with mp.Pool(args.workers) as pool:
        for gen in range(args.generations):
            batch = set()
            while len(batch) < args.batch:
                order = rng.choice(beam)[2]
                n = len(LOGICAL)
                if rng.randrange(3):
                    candidate = mutate(order[:n], rng) + order[n:]
                else:
                    candidate = order[:n] + mutate(order[n:], rng)
                if candidate not in seen:
                    batch.add(candidate)
            seen.update(batch)
            union = beam + pool.map(score, sorted(batch))
            rng.shuffle(union)
            union.sort(key=lambda x: x[0])
            beam = union[:args.width]
            if beam[0][0] < champion[0]:
                champion = beam[0]
                improvements.append({'generation': gen + 1, 'states': champion[0], 'order': champion[2]})
            report = {'kind': 'ics-order', 'seed': args.seed, 'width': args.width, 'batch': args.batch,
                      'generations': gen + 1, 'evaluations': len(seen), 'initial_states': initial_states,
                      'raw_states': champion[1], 'final_states': champion[0], 'order': champion[2],
                      'labels': [LABELS[i] for i in champion[2]], 'improvements': improvements}
            args.output.parent.mkdir(parents=True, exist_ok=True)
            args.output.write_text(json.dumps(report, indent=2) + '\n')
            print(f'generation {gen + 1}: {champion[0]}, frontier {beam[0][0]}..{beam[-1][0]}, evaluated {len(seen)}', flush=True)
    write_table(args.output.with_suffix('.tm'), build_ics(champion[2]))


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--seed', type=int, default=20260923)
    p.add_argument('--width', type=int, default=96)
    p.add_argument('--batch', type=int, default=192)
    p.add_argument('--generations', type=int, default=40)
    p.add_argument('--workers', type=int, default=4)
    p.add_argument('--initial', type=Path)
    p.add_argument('--output', type=Path, default=ROOT / 'scratch' / 'ics-order.json')
    run(p.parse_args())
