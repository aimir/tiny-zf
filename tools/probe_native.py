"""Replay bounded left-transfer, exposed-address and dispatch-scanner probes."""
import argparse
import json
from pathlib import Path
from types import SimpleNamespace

from machines import ROOT,count
from native import build_native
from native_addresses import build_addresses,expose
from instruction_tree import Trees,read_record
from register_check import compile_fragment
from search_native import PAIRS,REGISTERS,clean,family
from search_combined import fragment_bank,diverse_select
import search_pairing as engine

TERMINALS={'1.inc','1.decnz','1.sel','1.movr','1.movl','halt'}


def dispatch_contexts(machine):
    """Every root-to-call/jump path, including register-selector states.

    A normal primitive returns to break.0 with its end marker erased. A zero
    decrement instead returns to break.1. Jumps use their literal entry edge.
    The fixtures vary the instruction pointer; they assume valid native returns.
    """
    todo=[('main().0',())]
    while todo:
        state,path=todo.pop()
        for bit in (0,1):
            write,direction,target=machine.tm.states[(state,str(bit))];p=path+(bit,)
            ones={0}|{i+1 for i,b in enumerate(p) if b}
            if direction=='L':
                if write=='1':ones.add(len(p))
                else:ones.discard(len(p))
                yield target,len(p)-1,ones
            elif target in TERMINALS:
                if target=='halt':continue
                yield '6.break.0',len(p),ones
                if target=='1.decnz':yield '6.break.1',len(p),ones
            else:todo.append((target,p))


def dispatch_trace(edges,fixture):
    q,head,bits=fixture;bits=set(bits)
    for _ in range(10000):
        if q in TERMINALS:return q,head,frozenset(bits)
        edge=edges.get((q,str(int(head in bits))))
        if edge is None:return 'missing',q,head,frozenset(bits)
        write,direction,q=edge
        if write=='1':bits.add(head)
        else:bits.discard(head)
        head+=1 if direction=='R' else -1
    return None


def run_dispatch(base,initial):
    from joint import build_joint,decode
    m=build_joint(decode(base),sharing=base.get('shared_operations',False),grammar=base.get('grammar'),
                  formula_choices=base.get('formula_choices'),decoder=base.get('decoder'),
                  native=base.get('native'),instruction_tree=read_record(base,initial.parent))
    maximum=max(int(q.split('.')[-1]) for q,b in m.tm.states if q.startswith('4.dispatch.'))
    fixtures=list(dispatch_contexts(m));expected=[dispatch_trace(m.tm.states,f) for f in fixtures]
    if None in expected:raise ValueError('reference control trace exceeded its budget')
    results=[]
    for limit in range(maximum-1,0,-1):
        edges=dict(m.tm.states);edges[(f'4.dispatch.{limit}','0')]=('0','R','5.root')
        for i in range(limit+1,maximum+1):
            for bit in ('0','1'):edges.pop((f'4.dispatch.{i}',bit))
        failed=next((i for i,(f,e) in enumerate(zip(fixtures,expected)) if dispatch_trace(edges,f)!=e),None)
        results.append({'limit':limit,'first_failing_context':failed,'passed':failed is None})
    return {'reference_states':count(m.tm.states),'reference_limit':maximum,'contexts':len(fixtures),'results':results}


def run(args):
    base=json.loads(args.initial.read_text());args.output.parent.mkdir(parents=True,exist_ok=True)
    if args.mode=='dispatch':
        report=run_dispatch(base,args.initial);args.output.write_text(json.dumps(report,indent=2)+'\n');print(report,flush=True);return
    if args.mode=='left':
        rows=[]
        for a,b in PAIRS:
            for slot in (0,1,2):
                for eager in (False,True):
                    record=clean(base);remaining=[x for x in REGISTERS if x not in (a,b)]
                    order=remaining[:slot]+[a,b]+remaining[slot:]+['scratch3']
                    record['native']={'register_order':order,'moves':[[a,b]]};record['decoder']['eager']=eager
                    rows.append(engine.inspect_source(record,builder=build_native))
        source_evaluations=len(rows);source_best=min(r['final_states'] for r in rows)
        print('left grid',source_evaluations,'best',source_best,flush=True)
        rows=diverse_select(rows,8,lambda r:(r['final_states'],r['raw_states']),family)
        donor=fragment_bank(read_record(base,args.initial.parent));builder=build_native
        settings=SimpleNamespace(tree_generations=args.generations or 40,tree_batch=128,tree_width=32,tree_screen=3,memory_mb=512)
    else:
        from search_decoder import clean as clean_source
        record=clean_source(base);record['native_addresses']=True
        source=build_addresses(record);arena=Trees()
        root=arena.import_record(read_record(base,args.initial.parent),source.registers)
        root=expose(arena,root,list(source.registers));data=arena.export(root);arena.clear_caches()
        row=engine.inspect_source(record,builder=build_addresses);row['tree']=data
        rows=[row];donor={};builder=build_addresses;source_evaluations=1;source_best=row['final_states']
        settings=SimpleNamespace(tree_generations=args.generations or 150,tree_batch=192,tree_width=80,tree_screen=4,memory_mb=512)
    results=[];best=None
    for i,row in enumerate(rows):
        seed=(20260928 if args.mode=='left' else 20260929)+i
        result=engine.tree_search(row,donor,settings,seed,builder=builder);results.append(result)
        print(args.mode,'tree',i+1,'source',row['final_states'],'final',result['final_states'],flush=True)
        if best is None or (result['final_states'],result['raw_states'])<(best['final_states'],best['raw_states']):
            best=result;engine.save(args.output,best,best['tree'],builder=builder,kind='ics-native-'+args.mode+'-experiment')
    report={'mode':args.mode,'source_evaluations':source_evaluations,'best_source_states':source_best,
            'tree_mutation_attempts':sum(r['tree_attempts'] for r in results),
            'tree_full_reduction_evaluations':sum(r['tree_reductions'] for r in results),
            'best_states':best['final_states'],'peak_rss_mib':engine.memory_mb(),
            'finalists':[{k:v for k,v in r.items() if k!='tree'} for r in results]}
    args.output.with_suffix('.report.json').write_text(json.dumps(report,indent=2)+'\n')
    print(args.mode,'result',best['final_states'],flush=True)


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('mode',choices=('left','addresses','dispatch'))
    p.add_argument('--initial',type=Path,default=ROOT/'candidates/ics-best.json')
    p.add_argument('--output',type=Path)
    p.add_argument('--generations',type=int)
    args=p.parse_args()
    if args.generations is not None and args.generations<1:p.error('generations must be positive')
    args.output=args.output or ROOT/f'scratch/native-{args.mode}.json'
    run(args)
