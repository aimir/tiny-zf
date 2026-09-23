"""Beam search over layout, schema parameter naming and arithmetic lowering."""
import argparse
from functools import partial
import json
import multiprocessing as mp
from pathlib import Path
import random
from machines import ROOT, count, totalize, write_table
from ics import LOGICAL, LABELS
from joint import SCHEMAS, build_joint, encode, decode
from reduce import reduce
from search import mutate


def score(config, sharing=False, grammar=None, formula_choices=None):
    machine = build_joint(config, sharing=sharing, grammar=grammar, formula_choices=formula_choices)
    return len(reduce(totalize(machine.tm.start, machine.tm.states))), count(machine.tm.states), config


def mutation(config, rng, storage_search=False, encoding_search=False):
    order, permutations, protected, fusion, storage, reverse = config
    kind = rng.randrange(12 + int(storage_search) + int(encoding_search))
    if kind < 4:
        split = len(LOGICAL)
        if rng.randrange(3):
            order = mutate(order[:split], rng) + order[split:]
        else:
            order = order[:split] + mutate(order[split:], rng)
    elif kind < 10:
        permutations = list(permutations)
        for _ in range(1 if kind < 8 else rng.randrange(2, 5)):
            permutations[rng.randrange(len(permutations))] = rng.randrange(6)
        permutations = tuple(permutations)
    elif kind == 10:
        protected = rng.randrange(6)
    elif kind == 11:
        fusion = rng.randrange(-1, 8)
    elif kind == 12 and storage_search:
        storage = not storage
    else:
        reverse = not reverse
    if reverse and fusion == -1:
        fusion = rng.randrange(8)
    return order, permutations, protected, fusion, storage, reverse


def run(args):
    initial_record = json.loads(args.initial.read_text())
    if initial_record.get('decoder') or initial_record.get('native') is not None:raise ValueError('allocated source: use search_native.py for native layouts, otherwise search_decoder.py')
    if initial_record.get("instruction_tree"):
        print("Source search rebuilds the saved source; run search_tree.py on its output to optimize the changed tree.",flush=True)
    initial = decode(initial_record)
    sharing = getattr(args, "sharing", False) or initial_record.get("shared_operations", False)
    grammar = initial_record.get("grammar")
    formula_choices = initial_record.get("formula_choices")
    evaluate = partial(score, sharing=sharing, grammar=grammar, formula_choices=formula_choices)
    if args.fusion is not None:
        initial = (*initial[:3], args.fusion, *initial[4:])
    if args.storage:
        initial = (*initial[:4], True, initial[5])
    beam = [evaluate(initial)]
    champion = beam[0]
    initial_states = champion[0]
    seen = {initial}
    rng = random.Random(args.seed)
    history = []
    with mp.Pool(args.workers) as pool:
        for gen in range(args.generations):
            batch = set()
            while len(batch) < args.batch:
                candidate = mutation(rng.choice(beam)[2], rng, args.storage, args.encoding)
                if sharing and not candidate[4]:
                    continue
                if candidate not in seen:
                    batch.add(candidate)
            seen.update(batch)
            union = beam + pool.map(evaluate, sorted(batch))
            rng.shuffle(union)
            union.sort(key=lambda x:x[0])
            beam = union[:args.width]
            if beam[0][0] < champion[0]:
                champion = beam[0]
                history.append({'generation': gen+1, 'states':champion[0], **encode(champion[2])})
            report = {'kind':'ics-joint', 'shared_operations':sharing, 'grammar':grammar, 'formula_choices':formula_choices, 'seed':args.seed, 'width':args.width, 'batch':args.batch,
                      'generations':gen+1, 'evaluations':len(seen), 'initial_states':initial_states, 'storage_search':args.storage, 'encoding_search':args.encoding,
                      'raw_states':champion[1], 'final_states':champion[0], **encode(champion[2]),
                      'improvements':history}
            args.output.parent.mkdir(parents=True, exist_ok=True)
            args.output.write_text(json.dumps(report, indent=2)+'\n')
            if args.frontier:
                args.frontier.write_text(json.dumps([{'score':s, 'raw':r, 'shared_operations':sharing, 'grammar':grammar, 'formula_choices':formula_choices, **encode(c)} for s,r,c in beam],indent=2)+'\n')
            print(f'generation {gen+1}: {champion[0]}, frontier {beam[0][0]}..{beam[-1][0]}, {len(seen)} evaluated',flush=True)
    write_table(args.output.with_suffix('.tm'), build_joint(champion[2], sharing=sharing, grammar=grammar, formula_choices=formula_choices))


if __name__ == '__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--initial',type=Path,default=ROOT/'candidates/ics-best.json')
    p.add_argument('--fusion',type=int)
    p.add_argument('--storage',action='store_true')
    p.add_argument('--sharing',action='store_true')
    p.add_argument('--encoding',action='store_true')
    p.add_argument('--seed',type=int,default=20260924)
    p.add_argument('--width',type=int,default=128)
    p.add_argument('--batch',type=int,default=256)
    p.add_argument('--generations',type=int,default=60)
    p.add_argument('--workers',type=int,default=4)
    p.add_argument('--output',type=Path,default=ROOT/'scratch/ics-joint.json')
    p.add_argument('--frontier',type=Path)
    run(p.parse_args())
