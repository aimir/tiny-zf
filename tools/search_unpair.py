"""Search fused unpair source/kernel choices together with allocation and trees."""
import argparse
from copy import deepcopy
import itertools
import json
from pathlib import Path
import random
from types import SimpleNamespace
from machines import ROOT,require
from decoder import allocation_plan
from native import build_native
from search_native import clean,PAIRS,REGISTERS
from search_decoder import mutate_allocation
from search_combined import fingerprint,fragment_bank,diverse_select
from instruction_tree import read_record
import search_pairing as engine


def category(row):
    o=row['record']['native']['unpair']
    return 'native' if row['cantor_active'] else 'restore' if o['restore'] else 'reorder'


def family(row):
    o=row['record']['native']['unpair'];d=row['record']['decoder']
    return o['variant'],o['restore'],tuple(o.get('step_pair',())),tuple(d['order']),d['eager']


def repair(record):
    o=record['native'];u=o['unpair'];order=o['register_order']
    if u.get('step'):
        pair=u['step_pair'];order=pair+[x for x in order if x not in pair];o['register_order']=order
    o['moves']=[p for p in o['moves'] if abs(order.index(p[0])-order.index(p[1]))==1]
    return record


def mutate(record,rng):
    r=clean(record);o=r['native'];u=o['unpair'];kind=rng.randrange(12)
    if kind<6:
        r=mutate_allocation(r,rng);r['native']=o
    elif kind==6:u['variant']=rng.randrange(4)
    elif kind==7:u['restore']=rng.randrange(8)
    elif kind==8:
        u['step']=bool(rng.randrange(2));u['step_pair']=rng.choice([['scratch1','scratch2'],['topwff','scratch2']])
    elif kind==9:
        a,b=rng.sample(range(10),2);order=o['register_order'];order[a],order[b]=order[b],order[a]
    else:
        order=o['register_order'];pairs=[list(p) for p in PAIRS if abs(order.index(p[0])-order.index(p[1]))==1]
        if pairs:
            pair=rng.choice(pairs)
            if pair in o['moves']:o['moves'].remove(pair)
            else:o['moves'].append(pair)
    return repair(r)


def run(args):
    base=json.loads(args.initial.read_text());rng=random.Random(args.seed)
    original=read_record(base,args.initial.parent);donor=fragment_bank(original)
    args.output.parent.mkdir(parents=True,exist_ok=True)
    score=lambda r:(r['final_states'],r['raw_states'])
    seen=set();evaluations=invalid=0
    def evaluate(record):
        nonlocal evaluations,invalid
        try:plan=allocation_plan(record['decoder'])
        except (ValueError,StopIteration):invalid+=1;return None
        key=fingerprint(record)
        if key in seen:return None
        seen.add(key);evaluations+=1
        row=engine.inspect_source(record,builder=build_native);row['source_states']=row['final_states']
        engine.check_memory(args);return row
    baseline=clean(base);row=evaluate(baseline)
    settings=SimpleNamespace(**{**vars(args),'tree_generations':0})
    best=engine.tree_search({**row,'tree':original},{},settings,args.seed,builder=build_native)
    rows=[]
    for v,restore,pair,eager in itertools.product(range(4),range(8),(None,['scratch1','scratch2'],['topwff','scratch2']),(False,True)):
        if pair is None and restore==0 and v==0:continue
        r=clean(base);r['native']['unpair']={'variant':v,'restore':restore,'step':pair is not None,'step_pair':pair or ['scratch1','scratch2']}
        r['decoder']['eager']=eager
        row=evaluate(repair(r))
        if row:rows.append(row)
    quotas={'reorder':args.width//4,'restore':args.width//4,'native':args.width//2}
    def retain(rows,quotas):
        unique={}
        for r in rows:
            key=(r['source_hash'],category(r),r['raw_states'])
            if key not in unique or score(r)<score(unique[key]):unique[key]=r
        return sorted([r for name,n in quotas.items() for r in diverse_select([x for x in unique.values() if category(x)==name],n,score,family)],key=score)
    beam=retain(rows,quotas)
    def show(tag):print(tag,'evaluations',evaluations,'best',{k:min((r['final_states'] for r in beam if category(r)==k),default=None) for k in quotas},flush=True)
    show('grid')
    for generation in range(args.generations):
        trials=list(beam)
        for _ in range(args.batch):
            r=mutate(rng.choice(beam)['record'],rng);u=r['native']['unpair']
            if not u['step'] and not u['restore'] and not u['variant']:continue
            row=evaluate(r)
            if row:trials.append(row)
        beam=retain(trials,quotas)
        if score(beam[0])<score(best):best=beam[0]
        if (generation+1)%5==0:show('generation '+str(generation+1))
    finalists=retain(beam,{'reorder':args.tree_candidates//4,'restore':args.tree_candidates//4,'native':args.tree_candidates//2})
    results=[];families={}
    args.output.with_suffix('.frontier.json').write_text(json.dumps(finalists,indent=2)+'\n')
    for i,row in enumerate(finalists):
        result=engine.tree_search(row,donor,args,args.seed+100000+i,builder=build_native);results.append(result)
        name=category(result)
        print('tree',i+1,name,'source',row['source_states'],'final',result['final_states'],flush=True)
        if name not in families or score(result)<score(families[name]):
            families[name]=result
            engine.save(args.output.with_name(args.output.stem+'-'+name+'.json'),result,result['tree'],builder=build_native,kind='ics-fused-unpair-experiment')
        if score(result)<score(best):best=result
        engine.save(args.output,best,best.get('tree'),builder=build_native,kind='ics-fused-unpair-experiment')
        args.output.with_suffix('.frontier.json').write_text(json.dumps(results+finalists[i+1:],indent=2)+'\n')
    report={'arguments':vars(args),'source_evaluations':evaluations,'invalid_plans_rejected':invalid,
            'best_states':best['final_states'],'best_by_family':{k:r['final_states'] for k,r in families.items()},
            'tree_mutation_attempts':sum(r['tree_attempts'] for r in results),
            'tree_full_reduction_evaluations':sum(r['tree_reductions'] for r in results),'peak_rss_mib':engine.memory_mb(),
            'finalists':[{k:v for k,v in r.items() if k!='tree'} for r in results]}
    args.output.with_suffix('.report.json').write_text(json.dumps(report,indent=2,default=str)+'\n')
    print('result',report['best_by_family'],'incumbent',best['final_states'],flush=True)


def refine(args):
    """Reuse the entire incumbent tree only after a complete source CFG audit."""
    from register_check import compile_fragment
    from instruction_tree import Trees
    from verify_tree import equivalent_increment_cfg
    base=json.loads(args.initial.read_text());original=read_record(base,args.initial.parent)
    label='expansion' if args.expand_native_frontier else 'whole tree'
    rows=json.loads((args.whole_tree_refinement or args.expand_native_frontier).read_text());matched=[];results=[];best=None
    args.output.parent.mkdir(parents=True,exist_ok=True)
    for i,old in enumerate(rows):
        row=engine.inspect_source(old['record'],builder=build_native)
        if args.expand_native_frontier:
            if not row['native_active']:continue
            require(bool(old.get('tree')),'native expansion needs completed finalist trees')
            from unpair_fusion import expand_native_tree
            new_record,original=expand_native_tree(row['record'],old['tree'])
            row=engine.inspect_source(new_record,builder=build_native)
        # Adding/removing a kernel changes the fixed-state cost model. Keep
        # whole-tree transfer here to sources that emit only ordinary primitives.
        if row['native_active']:continue
        source=build_native(row['record']);target=build_native(row['record'],compile_machine=False)
        arena=Trees();root=arena.import_record(original,target.registers);arena.install(target,root)
        try:
            pairs=equivalent_increment_cfg(compile_fragment(source,source.find_seq('main().0'),terminal='return'),
                                          compile_fragment(target,target.find_seq('main().0'),terminal='return'))
        except ValueError:
            arena.clear_caches();continue
        arena.clear_caches();matched.append(i)
        result=engine.tree_search({**row,'tree':original},{},args,args.seed+100000+i,builder=build_native)
        result.update(source_index=i,**{('expanded_source_cfg_pairs' if args.expand_native_frontier else 'whole_tree_cfg_pairs'):pairs});results.append(result)
        print(label,i,'final',result['final_states'],flush=True)
        if best is None or (result['final_states'],result['raw_states'])<(best['final_states'],best['raw_states']):
            best=result;engine.save(args.output,best,best['tree'],builder=build_native,kind='ics-fused-unpair-expanded' if args.expand_native_frontier else 'ics-fused-unpair-whole-tree')
    require(bool(results),'no source finalist matches the whole incumbent tree')
    report={'arguments':vars(args),'matched_source_indices':matched,'best_states':best['final_states'],
            'tree_mutation_attempts':sum(r['tree_attempts'] for r in results),
            'tree_full_reduction_evaluations':sum(r['tree_reductions'] for r in results),'peak_rss_mib':engine.memory_mb(),
            'finalists':[{k:v for k,v in r.items() if k!='tree'} for r in results]}
    args.output.with_suffix('.report.json').write_text(json.dumps(report,indent=2,default=str)+'\n')
    print(label+' result',best['final_states'],flush=True)


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--initial',type=Path,default=ROOT/'candidates/ics-best.json')
    p.add_argument('--output',type=Path,default=ROOT/'scratch/unpair.json')
    p.add_argument('--expand-native-frontier',type=Path,help='expand tape primitives in completed finalist trees and score them again')
    p.add_argument('--whole-tree-refinement',type=Path,help='audit and refine compatible sources from this frontier using the entire incumbent tree')
    p.add_argument('--seed',type=int,default=20260924)
    p.add_argument('--generations',type=int,default=25)
    p.add_argument('--batch',type=int,default=256)
    p.add_argument('--width',type=int,default=128)
    p.add_argument('--tree-candidates',type=int,default=32)
    p.add_argument('--tree-generations',type=int,default=80)
    p.add_argument('--tree-batch',type=int,default=128)
    p.add_argument('--tree-width',type=int,default=48)
    p.add_argument('--tree-screen',type=int,default=4)
    p.add_argument('--memory-mb',type=int,default=512)
    args=p.parse_args()
    if min(args.batch,args.width,args.tree_candidates,args.tree_batch,args.tree_width,args.memory_mb)<1 or args.width%4 or args.tree_candidates%4:p.error('positive limits and widths divisible by four required')
    if min(args.generations,args.tree_generations,args.tree_screen)<0:p.error('negative search budget')
    if args.whole_tree_refinement and args.expand_native_frontier:p.error('choose only one refinement mode')
    (refine if args.whole_tree_refinement or args.expand_native_frontier else run)(args)
