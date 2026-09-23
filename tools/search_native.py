"""Joint native-kernel, register-placement, decoder and source/tree beam."""
import argparse
from copy import deepcopy
import itertools
import json
from pathlib import Path
import random
from types import SimpleNamespace

from machines import ROOT,require
from native import build_native
from decoder import allocation_plan
from instruction_tree import read_record
from search_combined import fingerprint,fragment_bank,diverse_select
from search_decoder import clean as clean_decoder,mutate_allocation
import search_pairing as engine

REGISTERS=('prooflist','nextproof','topwff','wffstack','axiomcode','param1','param2','param3','scratch1','scratch2')
# Source transfer opportunities; plans may introduce others during mutation.
PAIRS=(('scratch1','scratch2'),('scratch1','topwff'),('scratch2','topwff'),
       ('scratch2','wffstack'),('wffstack','scratch1'),('topwff','scratch2'),
       ('scratch1','param1'),('scratch1','param2'),('scratch1','param3'),
       ('scratch1','axiomcode'),('scratch1','nextproof'),('scratch2','prooflist'))


def clean(record):
    r=clean_decoder(record)
    r['native']=deepcopy(record.get('native') or {'register_order':[*REGISTERS,'scratch3'],'moves':[]})
    return r


def available(order):
    return [[a,b] for a,b in PAIRS if order.index(a)==order.index(b)+1]


def mutate(record,rng):
    r=clean(record);kind=rng.randrange(10)
    if kind<5:
        r2=mutate_allocation(r,rng);r2['native']=r['native'];r=r2
    else:
        o=r['native'];order=o['register_order']
        if kind<8:
            a,b=rng.sample(range(10),2);order[a],order[b]=order[b],order[a]
            o['moves']=[pair for pair in o['moves'] if pair in available(order)]
            if rng.randrange(2):o['moves']=available(order)
        else:
            moves=available(order)
            if moves:
                pair=rng.choice(moves)
                if pair in o['moves']:o['moves'].remove(pair)
                else:o['moves'].append(pair)
        if kind==9 and rng.randrange(2):
            a,b=rng.choice(PAIRS);rest=[x for x in REGISTERS if x not in (a,b)];rng.shuffle(rest)
            pos=rng.randrange(9);order=rest[:pos]+[b,a]+rest[pos:]+['scratch3']
            o['register_order']=order;o['moves']=available(order)
    return r


def family(row):
    native=row['record']['native'];moves=native['moves'];o=row['record']['decoder']
    return bool(moves),len(moves),tuple(tuple(x) for x in moves),tuple(o['order'])


def run(args):
    base=json.loads(args.initial.read_text());rng=random.Random(args.seed)
    require(not (base.get('native') or {}).get('unpair'),'use search_unpair.py to preserve fused arithmetic')
    original=read_record(base,args.initial.parent);donor=fragment_bank(original) if original else {}
    args.output.parent.mkdir(parents=True,exist_ok=True)
    seen=set();evaluations=invalid=0;all_best={};loaded=[]
    score=lambda r:(r['final_states'],r['raw_states'])
    enabled=lambda r:bool(r['record']['native']['moves']) if args.configured_pools else r['native_active']

    def evaluate(record):
        nonlocal evaluations,invalid
        try:plan=allocation_plan(record['decoder'])
        except (ValueError,StopIteration):invalid+=1;return None
        key=fingerprint((record,plan))
        if key in seen:return None
        seen.add(key);evaluations+=1
        row=engine.inspect_source(record,builder=build_native)
        row['source_states']=row['final_states']
        engine.check_memory(args)
        return row

    def retain(rows):
        # Keep ordinary and native candidates separately so an initial native
        # cost penalty cannot exclude the whole new operation family.
        if args.distinct_sources:
            unique={}
            for r in rows:
                key=(r['source_hash'],tuple(sorted(tuple(p) for p in r['record']['native']['moves'])),r['source_states'])
                if key not in unique or score(r)<score(unique[key]):unique[key]=r
            rows=list(unique.values())
        out=[]
        pools=((True,args.width),) if args.require_native else ((False,args.width//2),(True,args.width-args.width//2))
        for mode,quota in pools:
            group=[r for r in rows if enabled(r)==mode]
            out.extend(diverse_select(group,quota,score,family))
        return sorted(out,key=score)

    if args.resume_frontier:
        for old in json.loads(args.resume_frontier.read_text()):
            row=evaluate(clean(old['record']))
            if row:
                if old.get('tree'):
                    opts=SimpleNamespace(**{**vars(args),'tree_generations':0})
                    row=engine.tree_search({**row,'tree':old['tree']},{},opts,args.seed,builder=build_native)
                loaded.append(row)
    else:
        row=evaluate(clean(base))
        if original:
            opts=SimpleNamespace(**{**vars(args),'tree_generations':0})
            row=engine.tree_search({**row,'tree':original},{},opts,args.seed,builder=build_native)
        loaded.append(row)
        # Exhaust all triples involving the shared scratch pair near the cheap
        # end of the selector chains, then perturb placement and allocation.
        for third in (r for r in REGISTERS if r not in ('scratch1','scratch2')):
            for front in itertools.permutations(('scratch1','scratch2',third)):
                r=clean(base);order=list(front)+[x for x in REGISTERS if x not in front]+['scratch3']
                r['native']={'register_order':order,'moves':available(order)}
                if r['native']['moves']:
                    row=evaluate(r)
                    if row:loaded.append(row)
        for _ in range(args.grid):
            r=mutate(rng.choice(loaded)['record'],rng);row=evaluate(r)
            if row:loaded.append(row)
    require(bool(loaded),'empty native population')
    best=min(loaded,key=score);beam=retain(loaded)
    require(bool(beam),'no active native candidates in the supplied population')
    def show(tag):
        values={str(mode):min((r['final_states'] for r in beam if enabled(r)==mode),default=None) for mode in (False,True)}
        print(tag,'evaluations',evaluations,'best by native enabled',values,flush=True)
    show('grid')
    for generation in range(args.generations):
        trials={fingerprint(r['record']):r for r in beam}
        for _ in range(args.batch):
            row=evaluate(mutate(rng.choice(beam)['record'],rng))
            if row:trials[fingerprint(row['record'])]=row
        beam=retain(list(trials.values()))
        if score(beam[0])<score(best):best=beam[0]
        if (generation+1)%5==0:show(f'generation {generation+1}')
    finalists=[]
    for mode in ((True,) if args.require_native else (False,True)):
        quota=args.tree_candidates if args.require_native else args.tree_candidates//2
        finalists+=diverse_select([r for r in beam if enabled(r)==mode],quota,score,family)
    args.output.with_suffix('.frontier.json').write_text(json.dumps(finalists,indent=2)+'\n')
    results=[]
    for i,row in enumerate(finalists):
        result=engine.tree_search(row,donor,args,args.seed+100000+i,builder=build_native);results.append(result)
        print('tree',i+1,'native',bool(row['record']['native']['moves']),'source',row['source_states'],'final',result['final_states'],flush=True)
        if score(result)<score(best):best=result
        key='native' if enabled(result) else 'ordinary'
        if key not in all_best or score(result)<score(all_best[key]):
            all_best[key]=result;engine.save(args.output.with_name(args.output.stem+'-'+key+'.json'),result,result.get('tree'),builder=build_native,kind='ics-native-experiment')
        engine.save(args.output,best,best.get('tree'),builder=build_native,kind='ics-native-experiment')
        args.output.with_suffix('.frontier.json').write_text(json.dumps(results+finalists[i+1:],indent=2)+'\n')
    report={'arguments':vars(args),'source_evaluations':evaluations,'invalid_plans_rejected':invalid,
            'best_states':best['final_states'],'best_by_family':{k:v['final_states'] for k,v in all_best.items()},
            'tree_mutation_attempts':sum(r['tree_attempts'] for r in results),
            'tree_full_reduction_evaluations':sum(r['tree_reductions'] for r in results),
            'peak_rss_mib':engine.memory_mb(),
            'finalists':[{k:v for k,v in r.items() if k!='tree'} for r in results]}
    args.output.with_suffix('.report.json').write_text(json.dumps(report,indent=2,default=str)+'\n')
    print('result',report['best_by_family'],flush=True)


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--initial',type=Path,default=ROOT/'candidates/ics-best.json')
    p.add_argument('--output',type=Path,default=ROOT/'scratch/native.json')
    p.add_argument('--resume-frontier',type=Path)
    p.add_argument('--require-native',action='store_true',help='reserve the whole source beam and final shortlist for emitted native kernels')
    p.add_argument('--distinct-sources',action='store_true',help='deduplicate identical compiler trees, bindings and source scores')
    p.add_argument('--configured-pools',action='store_true',help='replay the initial pilot that classified configurations instead of emitted kernels')
    p.add_argument('--seed',type=int,default=20260927)
    p.add_argument('--grid',type=int,default=512)
    p.add_argument('--generations',type=int,default=30)
    p.add_argument('--batch',type=int,default=256)
    p.add_argument('--width',type=int,default=128)
    p.add_argument('--tree-candidates',type=int,default=32)
    p.add_argument('--tree-generations',type=int,default=100)
    p.add_argument('--tree-batch',type=int,default=128)
    p.add_argument('--tree-width',type=int,default=48)
    p.add_argument('--tree-screen',type=int,default=3)
    p.add_argument('--memory-mb',type=int,default=512)
    args=p.parse_args()
    if min(args.batch,args.width,args.tree_candidates,args.tree_batch,args.tree_width,args.memory_mb)<2 or args.tree_candidates%2:p.error('invalid positive/even beam limits')
    if min(args.generations,args.grid,args.tree_generations,args.tree_screen)<0:p.error('invalid search limits')
    run(args)
