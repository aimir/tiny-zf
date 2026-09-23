"""Compare dyadic encodings using source beams and fully reduced tree finalists.

Outputs are experiments, never automatic replacements for the incumbent.
The tree checker compares each result with its own recoded source, not with
the incumbent's different arithmetic. See docs/PAIRING.md for the contracts.
"""
import argparse
from copy import deepcopy
import hashlib
import itertools
import json
from pathlib import Path
import random
import resource
import sys

from machines import ROOT, count, totalize, write_table
from reduce import reduce
from pairing import build_pairing, KERNELS
from search_combined import (gene_of, source_record, mutate, fingerprint,
                             fragment_bank, transfer_fragments, diverse_select)
from instruction_tree import Trees, read_record
from register_check import compile_fragment
from verify_tree import equivalent_increment_cfg
from grammar import equivalent_cfg


def memory_mb():
    return resource.getrusage(resource.RUSAGE_SELF).ru_maxrss/(1024**2 if sys.platform=='darwin' else 1024)


def check_memory(args):
    if memory_mb()>args.memory_mb:
        raise MemoryError('cooperative pairing-search resident-memory budget exceeded')


def family(row):
    p = row['record']['pairing']
    return p['kernel'], p['tags'], p['positive_inverse'], tuple(p['tag_order']), p.get('dual',False)


def clean(record):
    return {**source_record(gene_of(record)), 'pairing': deepcopy(record.get('pairing', {}))}


def inspect_source(record):
    machine = build_pairing(record)
    arena = Trees(); root = arena.import_machine(machine)
    digest = fingerprint(arena.export(root)); arena.clear_caches()
    raw = count(machine.tm.states)
    return {'record': record, 'raw_states': raw,
            'final_states': len(reduce(totalize(machine.tm.start, machine.tm.states))),
            'source_hash': digest}


def save(path, row, tree=None):
    record = row['record']
    machine = build_pairing(record)
    tree_path = path.with_suffix('.tree.json')
    if tree is not None:
        arena = Trees(); root = arena.import_record(tree, machine.registers)
        machine = build_pairing(record, compile_machine=False)
        arena.install(machine, root); machine.name_sequences(); machine.generate(); machine.tm.gc()
        tree_path.write_text(json.dumps(tree, indent=2)+'\n')
        arena.clear_caches()
    write_table(path.with_suffix('.tm'), machine)
    raw = count(machine.tm.states)
    final = len(reduce(totalize(machine.tm.start, machine.tm.states)))
    assert (raw, final) == (row['raw_states'], row['final_states'])
    data = {**record, 'kind': 'ics-dyadic-experiment',
            'status': 'experimental; computational checks only; not formally verified',
            'raw_states': raw, 'final_states': final,
            'table_sha256': hashlib.sha256(path.with_suffix('.tm').read_bytes()).hexdigest()}
    if tree is not None:
        data.update(instruction_tree=tree_path.name,
                    instruction_tree_sha256=hashlib.sha256(tree_path.read_bytes()).hexdigest())
    path.write_text(json.dumps(data, indent=2)+'\n')


def tree_search(row, donor, args, seed):
    machine = build_pairing(row['record'])
    original = compile_fragment(machine, machine.find_seq('main().0'), terminal='return')
    plain = build_pairing({**row['record'], 'grammar': None}, compile_machine=False)
    plain.main()
    equivalent_cfg(compile_fragment(plain, plain.find_seq('main().0'), terminal='return'), original)
    arena = Trees('general', True, 1); root = arena.import_machine(machine)
    fixed_states = count(machine.tm.states)-arena.size(root)
    roots = [root]
    if row.get('tree'):
        roots.append(arena.import_record(row['tree'], machine.registers))
    root2, transferred = transfer_fragments(arena, root, donor)
    if root2 != root: roots.append(root2)
    rng = random.Random(seed); beam = list(dict.fromkeys(roots)); cached = {}; best = None
    reductions = attempts = 0

    def inspect(v, audit=False):
        nonlocal reductions, best
        data = arena.export(v); key = fingerprint(data)
        if key in cached: return cached[key]
        m = build_pairing(row['record'], compile_machine=False)
        arena.install(m, v); m.name_sequences(); m.generate(); m.tm.gc()
        raw = count(m.tm.states); final = len(reduce(totalize(m.tm.start, m.tm.states)))
        if raw != fixed_states+arena.size(v):
            raise ValueError('raw state-count model disagrees with compiled table')
        reductions += 1
        result = (final, raw)
        cached[key] = result
        improves = best is None or result < (best['final_states'], best['raw_states'])
        if audit or improves:
            pairs = equivalent_increment_cfg(original, compile_fragment(m, m.find_seq('main().0'), terminal='return'))
        if improves:
            best = {**row, 'raw_states': raw, 'final_states': final, 'tree': data,
                    'matched_segment_pairs': pairs}
        return result

    for v in beam: inspect(v,audit=True)
    for generation in range(args.tree_generations):
        trials = set(beam); moves = {}
        for _ in range(args.tree_batch):
            current = rng.choice(beam)
            for _ in range(1 if rng.randrange(4) else rng.randrange(2,5)):
                choices = []
                for v in sorted(arena.reachable(current)):
                    if v not in moves: moves[v] = tuple(arena.rotations(v))
                    choices.extend((v,w) for w in moves[v])
                if not choices: break
                v,w = rng.choice(choices)
                if rng.randrange(4) == 0:
                    parents = [p for p in sorted(arena.reachable(current)) if v in arena.nodes[p]]
                    if parents:
                        p = rng.choice(parents); a,b = arena.nodes[p]
                        w = arena.node(w if a == v else a, w if b == v else b); v = p
                current = arena.replace(current, v, w)
            trials.add(current); attempts += 1
        scores = [(arena.size(v),v) for v in sorted(trials)]
        rng.shuffle(scores); scores.sort(key=lambda x:x[0]); beam=[]
        for delta,quota in [(0,args.tree_width//2),(1,args.tree_width//4),(2,args.tree_width//4)]:
            beam.extend([v for n,v in scores if n == scores[0][0]+delta][:quota])
        beam.extend(v for _,v in scores if v not in beam and len(beam)<args.tree_width)
        for _,v in scores[:args.tree_screen]: inspect(v)
        old=arena; arena,beam=old.compact(beam); old.clear_caches()
        check_memory(args)
    for v in beam: inspect(v)
    arena.clear_caches()
    return {**best, 'tree_attempts': attempts, 'tree_reductions': reductions,
            'transferred_fragments': transferred, 'tree_seed': seed}


def run(args):
    args.output.parent.mkdir(parents=True, exist_ok=True)
    baseline = json.loads(args.initial.read_text())
    rng = random.Random(args.seed); seen = set(); unique = {}; evaluations = 0
    initial_tree = read_record(baseline, args.initial.parent)
    donor = fragment_bank(initial_tree) if initial_tree else {}
    beam = []

    def evaluate(record):
        nonlocal evaluations
        if record.get('fusion', -1)<0:record={**record,'fusion':0}
        key = fingerprint(record)
        if key in seen: return None
        seen.add(key); evaluations += 1
        row = inspect_source(record)
        check_memory(args)
        unique.setdefault(row['source_hash'], row)
        return row

    if args.resume_frontier:
        # Rebuild all saved source records. Trees are checked during optimization.
        old = json.loads(args.resume_frontier.read_text())
        for row in old:
            checked = evaluate(row['record'])
            if checked is not None:
                beam.append({**checked, **({'tree':row['tree']} if row.get('tree') else {})})
    else:
        for kernel, inverse, tags, reverse, tag_order in itertools.product(
                KERNELS, (False, True), ('generic','alternating','repeat1','repeat2'),
                (False,True), itertools.permutations((2,3,4))):
            for fusion in (range(8) if tags == 'generic' else (0,1)):
                record=clean(baseline); record['fusion']=fusion; record['reverse_payload']=reverse
                record['pairing']={'kernel':kernel, 'positive_inverse':inverse,
                                   'tags':tags, 'tag_order':tag_order, 'dual':args.dual}
                row=evaluate(record)
                if row is not None: beam.append(row)
                if evaluations%200==0:
                    print('grid progress',evaluations,'best',min(r['final_states'] for r in beam),flush=True)
        print('grid',evaluations,'best',min(r['final_states'] for r in beam),flush=True)
    score=lambda r:(r['final_states'],r['raw_states'])
    beam=diverse_select(list({r['source_hash']:r for r in beam}.values()),args.width,score,family)
    best=min(beam,key=score)
    for generation in range(args.generations):
        trials={r['source_hash']:r for r in beam}
        for _ in range(args.batch):
            parent=rng.choice(beam); record=clean(parent['record'])
            if rng.randrange(5):
                record={**source_record(mutate(gene_of(record),rng)), 'pairing':record['pairing']}
            else:
                options=record['pairing']; choice=rng.randrange(4)
                if choice==0:options['kernel']=rng.choice(tuple(KERNELS))
                elif choice==1:options['positive_inverse']=not options['positive_inverse']
                elif choice==2:options['tags']=rng.choice(('generic','alternating','repeat1','repeat2'))
                else:options['tag_order']=rng.sample((2,3,4),3)
            row=evaluate(record)
            if row is not None:trials[row['source_hash']]=row
        beam=diverse_select(list(trials.values()),args.width,score,family)
        if score(beam[0])<score(best):
            best=beam[0]; save(args.output,best)
        if (generation+1)%5==0:
            print('generation',generation+1,'evaluations',evaluations,'best',best['final_states'],flush=True)
    finalists=diverse_select(beam,args.tree_candidates,score,family)
    args.output.with_suffix('.frontier.json').write_text(json.dumps(finalists,indent=2)+'\n')
    results=[]
    for i,row in enumerate(finalists):
        result=tree_search(row,donor,args,args.seed+100000+i); results.append(result)
        print('tree',i+1,'source',row['final_states'],'final',result['final_states'],flush=True)
        if score(result)<score(best) or not args.output.exists():
            best=result; save(args.output,best,best.get('tree'))
        args.output.with_suffix('.frontier.json').write_text(json.dumps(results+finalists[i+1:],indent=2)+'\n')
    save(args.output,best,best.get('tree'))
    report={'seed':args.seed,'arguments':vars(args).copy(),'source_evaluations':evaluations,
            'unique_source_trees':len(unique),'best_states':best['final_states'],
            'tree_attempts':sum(r['tree_attempts'] for r in results),
            'tree_reductions':sum(r['tree_reductions'] for r in results),
            'peak_rss_mib':memory_mb(),
            'finalists':[{k:v for k,v in r.items() if k!='tree'} for r in results]}
    args.output.with_suffix('.report.json').write_text(json.dumps(report,indent=2,default=str)+'\n')
    print('result',args.output,'states',best['final_states'],flush=True)


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--initial',type=Path,default=ROOT/'candidates/ics-best.json')
    p.add_argument('--output',type=Path,default=ROOT/'scratch/pairing.json')
    p.add_argument('--resume-frontier',type=Path)
    p.add_argument('--dual',action='store_true',help='use reversed dyadic pairing except for outer tags')
    p.add_argument('--seed',type=int,default=20260923)
    p.add_argument('--generations',type=int,default=30)
    p.add_argument('--batch',type=int,default=128)
    p.add_argument('--width',type=int,default=64)
    p.add_argument('--tree-candidates',type=int,default=12)
    p.add_argument('--tree-generations',type=int,default=80)
    p.add_argument('--tree-batch',type=int,default=128)
    p.add_argument('--tree-width',type=int,default=32)
    p.add_argument('--tree-screen',type=int,default=2)
    p.add_argument('--memory-mb',type=int,default=512,help='cooperative process RSS budget, checked between evaluations/generations')
    args=p.parse_args()
    if min(args.batch,args.width,args.tree_candidates,args.tree_batch,args.tree_width,args.memory_mb)<1 or min(args.generations,args.tree_generations,args.tree_screen)<0:
        p.error('invalid search limits')
    run(args)
