"""Bounded source/allocation beam followed by final-score tree search."""
import argparse
from copy import deepcopy
import itertools
from types import SimpleNamespace
import json
from pathlib import Path
import random

from decoder import FIELDS, REGS, default_options, allocation_plan, build_decoder
from machines import ROOT, require
from instruction_tree import read_record
from search_combined import (gene_of,source_record,mutate,fingerprint,
                            fragment_bank,diverse_select)
# Reuse the tree engine with an explicit builder; no arithmetic is substituted.
import search_pairing as tree_engine


def family(row):
    o=row['record']['decoder']
    direct=sum(s[0]==d for s,d in zip(o['stages'],o['order']))
    return o.get('packed_counter',False),o.get('borrow_stack',False),o.get('defer_heads',False),o.get('restore_tail',True),o['eager'],direct,tuple(o['order'])


def clean(record):
    return {**source_record(gene_of(record)),'decoder':deepcopy(record.get('decoder',default_options()))}


def mutate_allocation(record,rng):
    r=clean(record);o=r['decoder'];k=rng.randrange(14)
    if k<5:
        i=rng.randrange(4);j=rng.randrange(2)
        o['stages'][i][j]=rng.randrange(30) if rng.randrange(3) else rng.choice(REGS)
    elif k<7:
        i=rng.randrange(4);o['stages'][i][2]=not o['stages'][i][2]
    elif k==7:o['eager']=not o['eager']
    elif k==8:o['restore_tail']=not o.get('restore_tail',True)
    elif k==9:o['defer_heads']=not o.get('defer_heads',False)
    elif k==10:rng.shuffle(o['clear_order'])
    elif k==11:rng.shuffle(o['order'])
    else:r={**source_record(mutate(gene_of(r),rng)),'decoder':o}
    return r


def grid(base):
    # Direct writes, rotating tail buffers, independent transfer order, and
    # eager/lazy clears. Every field subset receives both tail strategies.
    for direct,rotate,eager in itertools.product(range(16),(False,True),(False,True)):
        for copy_mask in (0,15):
            r=clean(base);o=r['decoder']=default_options()
            o['eager']=eager;o['restore_tail']=not rotate
            o['stages']=[[FIELDS[i] if direct>>i&1 else 'scratch1',
                          'scratch2' if not rotate or not i%2 else 'prooflist',
                          bool(copy_mask>>i&1)] for i in range(4)]
            yield r
    for order,copy_mask in itertools.product(itertools.permutations(FIELDS),range(16)):
        r=clean(base);o=r['decoder']=default_options();o['clear_order']=list(order)
        o['stages']=[['scratch1','scratch2',bool(copy_mask>>i&1)] for i in range(4)]
        yield r
    # Deferred placements: keep heads in their allocated locations through all
    # four splits, then solve the parallel register assignment.
    rng=random.Random(4917)
    for _ in range(512):
        r=clean(base);o=r['decoder']=default_options()
        o.update(defer_heads=True,eager=bool(rng.randrange(2)),restore_tail=False)
        o['stages']=[[rng.randrange(30),rng.randrange(30),False] for _ in range(4)]
        yield r


def run(args):
    rng=random.Random(args.seed);base=json.loads(args.initial.read_text())
    require(base.get('native') is None,'native layout present: use search_native.py to preserve it')
    args.output.parent.mkdir(parents=True,exist_ok=True)
    seen=set();plans=set();evaluations=invalid=0;unique=set();beam=[]
    initial_tree=read_record(base,args.initial.parent)
    donor=fragment_bank(initial_tree) if initial_tree else {}
    score=lambda r:(r['final_states'],r['raw_states'])

    def evaluate(record):
        nonlocal evaluations,invalid
        try:plan=allocation_plan(record['decoder'])
        except (ValueError,StopIteration):invalid+=1;return None
        key=fingerprint((source_record(gene_of(record)),plan,
                         record['decoder'].get('borrow_stack',False),record['decoder'].get('packed_counter',False)))
        if key in seen:return None
        seen.add(key);plans.add(fingerprint(plan));evaluations+=1
        row=tree_engine.inspect_source(record,builder=build_decoder);unique.add(row['source_hash'])
        tree_engine.check_memory(args)
        return row

    def restore_tree(row, tree):
        # Audit and score saved trees before source selection; a good tree must
        # not disappear just because its compiler-generated source scores worse.
        settings=SimpleNamespace(**{**vars(args),'tree_generations':0})
        return tree_engine.tree_search({**row,'tree':tree},{},settings,args.seed,builder=build_decoder)

    if args.resume_frontier:
        for r in json.loads(args.resume_frontier.read_text()):
            row=evaluate(r['record'])
            if row:
                if r.get('tree'):row=restore_tree(row,r['tree'])
                beam.append(row)
    else:
        if ('decoder' in base
            and bool(base['decoder'].get('packed_counter'))==args.packed_counter
            and bool(base['decoder'].get('borrow_stack'))==args.borrow_stack):
            row=evaluate(clean(base))
            if row:
                if initial_tree:row=restore_tree(row,initial_tree)
                beam.append(row)
        for r in grid(base):
            r['decoder']['borrow_stack']=args.borrow_stack
            r['decoder']['packed_counter']=args.packed_counter
            row=evaluate(r)
            if row:beam.append(row)
        print('grid',evaluations,'best',min(r['final_states'] for r in beam),flush=True)
    require(bool(beam),'empty decoder population')
    beam=diverse_select(beam,args.width,score,family);best=min(beam,key=score)
    for gen in range(args.generations):
        candidates={r['source_hash']:r for r in beam}
        for _ in range(args.batch):
            r=evaluate(mutate_allocation(rng.choice(beam)['record'],rng))
            if r:candidates[r['source_hash']]=r
        beam=diverse_select(list(candidates.values()),args.width,score,family)
        if score(beam[0])<score(best):best=beam[0]
        if (gen+1)%5==0:print('generation',gen+1,'evaluations',evaluations,'best',best['final_states'],flush=True)
    finalists=diverse_select(beam,args.tree_candidates,score,family)
    results=[]
    args.output.with_suffix('.frontier.json').write_text(json.dumps(finalists,indent=2)+'\n')
    for i,row in enumerate(finalists):
        r=tree_engine.tree_search(row,donor,args,args.seed+100000+i,builder=build_decoder);results.append(r)
        print('tree',i+1,'source',row['final_states'],'final',r['final_states'],flush=True)
        if score(r)<score(best):best=r
        tree_engine.save(args.output,best,best.get('tree'),builder=build_decoder,kind='ics-decoder-experiment')
        args.output.with_suffix('.frontier.json').write_text(json.dumps(results+finalists[i+1:],indent=2)+'\n')
    tree_engine.save(args.output,best,best.get('tree'),builder=build_decoder,kind='ics-decoder-experiment')
    report={'arguments':vars(args),'source_evaluations':evaluations,
            'unique_source_trees':len(unique),'distinct_decoder_plans':len(plans),
            'invalid_plans_rejected':invalid,'best_states':best['final_states'],
            'tree_mutation_attempts':sum(r['tree_attempts'] for r in results),
            'tree_full_reduction_evaluations':sum(r['tree_reductions'] for r in results),
            'peak_rss_mib':tree_engine.memory_mb(),
            'finalists':[{k:v for k,v in r.items() if k!='tree'} for r in results]}
    args.output.with_suffix('.report.json').write_text(json.dumps(report,indent=2,default=str)+'\n')
    print('result',best['final_states'],flush=True)


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--initial',type=Path,default=ROOT/'candidates/ics-best.json')
    p.add_argument('--output',type=Path,default=ROOT/'scratch/decoder.json')
    p.add_argument('--resume-frontier',type=Path)
    p.add_argument('--borrow-stack',action='store_true')
    p.add_argument('--packed-counter',action='store_true')
    p.add_argument('--seed',type=int,default=20260925)
    p.add_argument('--generations',type=int,default=50)
    p.add_argument('--batch',type=int,default=192)
    p.add_argument('--width',type=int,default=80)
    p.add_argument('--tree-candidates',type=int,default=16)
    p.add_argument('--tree-generations',type=int,default=100)
    p.add_argument('--tree-batch',type=int,default=128)
    p.add_argument('--tree-width',type=int,default=40)
    p.add_argument('--tree-screen',type=int,default=2)
    p.add_argument('--memory-mb',type=int,default=512)
    args=p.parse_args()
    if args.borrow_stack and args.packed_counter:p.error('conflicting top-register uses')
    if min(args.batch,args.width,args.tree_candidates,args.tree_batch,args.tree_width,args.memory_mb)<1 or min(args.generations,args.tree_generations,args.tree_screen)<0:p.error('invalid search limits')
    run(args)
