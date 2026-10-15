"""Synthesize both rows of a merged state using contextual semantic menus.

One row is chosen from the intersection of previously accepted alternatives;
the other is synthesized in the resulting table, so it need not have been a
valid independent rewrite. Native execution is only a filter. Emitted tables
pass all pinned Python instruction cases and exact blank-tape bootstrap.
Instruction-valid tables with a different bootstrap are retained separately
as unproved research candidates, together with their finite tape shape.
"""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import time

from instruction_tree import Trees
from mira_global import Oracle,BOX_KERNEL,state_key,save_json,checkpoint_identity,bootstrap,write_table
from mira_global_native import NativeOracle
from mira_global_transfer import read


def pair_search_identity(folder,options_path,include_original,include_bootstrap):
    """Bind the resume offset to exactly the same ordered synthesis jobs."""
    identity=dict(version=1,options_sha256=hashlib.sha256(options_path.read_bytes()).hexdigest(),
                  include_original=include_original,include_bootstrap=include_bootstrap)
    path=folder/'search_identity.json'
    if path.exists():
        if json.loads(path.read_text())!=identity:
            raise ValueError('pair checkpoint uses different transition options or search flags')
    elif (folder/'progress.json').exists():
        raise ValueError('legacy pair checkpoint lacks a search identity; use a new output folder')
    save_json(path,identity)


def prune(table):
    todo=['0'];seen=set()
    while todo:
        q=todo.pop()
        if q=='254' or q in seen:continue
        seen.add(q)
        todo.extend(table[q,b][2]for b in(0,1))
    return {key:edge for key,edge in table.items()if key[0]in seen}


def bootstrap_root(table,minimum_gap=62,limit=2000000):
    """Find a broader root configuration; this does not prove initialization.

    The physical registers may initialize d, proof-length, and next-proof to
    arbitrary naturals. All other named registers and trailing registers must
    be zero. A formal soundness/completeness initialization lemma is still
    required before accepting a machine on this basis.
    """
    tape=set();q='0';head=0;last=None
    for step in range(limit+1):
        if q=='96':
            positions=sorted(p-head for p in tape)
            if positions and positions[0]==-1 and len(positions)>1 and positions[1]>=minimum_gap:
                gap=positions[1];cursor=gap+2;values=[];index=2
                while index<len(positions) and positions[index]==cursor:
                    length=1;index+=1
                    while index<len(positions) and positions[index]==cursor+length:
                        length+=1;index+=1
                    values.append(length-1);cursor+=length+1
                if index==len(positions):
                    last=dict(steps=step,head=head,gap=gap,registers=values[:9],
                              trailing_registers=values[9:])
                    if len(values)>=9 and all(v==0 for i,v in enumerate(values)if i not in(1,5,6)):
                        return dict(status='unproved_root',**last)
        if step==limit:break
        edge=table.get((q,int(head in tape)))
        if edge is None:
            return dict(status='halted_before_root',steps=step,state=q,last_root_shape=last)
        w,d,q=edge
        if w:tape.add(head)
        else:tape.discard(head)
        head+=1 if d=='R' else -1
    return dict(status='no_root_within_fuel',steps=limit,last_root_shape=last)


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--upstream',type=Path,required=True);p.add_argument('--table',type=Path,required=True)
    p.add_argument('--tree',type=Path);p.add_argument('--options',type=Path,required=True)
    p.add_argument('--output',type=Path,required=True);p.add_argument('--native',type=Path,required=True)
    p.add_argument('--fast-bootstrap',type=Path);p.add_argument('--d0',type=int,default=40)
    p.add_argument('--include-original',action='store_true');p.add_argument('--include-bootstrap',action='store_true')
    args=p.parse_args();tr=root=None
    if args.tree:
        data=json.loads(args.tree.read_text());tr=Trees()
        for i,pair in enumerate(data['nodes']):assert tr.node(*pair)==i
        root=data['root']
    table=read(args.table)
    py=Oracle(args.upstream,tr,root,table,d0=args.d0)
    py.protected=BOX_KERNEL;py.mutable_anchor_rows=frozenset([('3',0),('6',0),('48',0),('69',1)])
    checkpoint_identity(py,args.options.parent)
    oracle=NativeOracle(py,args.native);args.output.mkdir(parents=True,exist_ok=True)
    checkpoint_identity(oracle,args.output)
    pair_search_identity(args.output,args.options,args.include_original,args.include_bootstrap)
    options=json.loads(args.options.read_text())
    fast_boot=bootstrap
    if args.fast_bootstrap:
        spec=importlib.util.spec_from_file_location('mira_pair_bootstrap',args.fast_bootstrap)
        module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
        fast_boot=module.bootstrap
        assert fast_boot(table)==bootstrap(table)
    states=sorted({q for q,b in table},key=state_key)
    jobs=[]
    for i,a in enumerate(states):
        for b in states[:i]:
            if a in BOX_KERNEL and b in BOX_KERNEL:continue
            if not args.include_bootstrap and '8'in(a,b):continue
            q,s=(b,a)if a in BOX_KERNEL else(a,b)
            normalize=lambda e:(e[0],e[1],s if e[2]==q else e[2])
            affected=set().union(*(oracle.by_edge[v,r]for v in(q,s)for r in(0,1)))
            for fixed in(0,1):
                left={normalize(e)for e in options[f'{q}:{fixed}']}
                right={normalize(e)for e in options[f'{s}:{fixed}']}
                if s in BOX_KERNEL and(s,fixed)not in py.mutable_anchor_rows:
                    right={normalize(table[s,fixed])}
                for edge in sorted(left&right):
                    if not args.include_original and edge==table[q,fixed]==table[s,fixed]:continue
                    jobs.append((len(affected),q,s,fixed,edge,tuple(sorted(affected))))
    jobs.sort();progress=args.output/'progress.json'
    old=json.loads(progress.read_text())if progress.exists()else{}
    offset=old.get('completed_jobs',0);trials=old.get('trials',0);body_passes=old.get('body_passes',0)
    began=time.monotonic()
    print('jobs',len(jobs),'resume',offset,flush=True)
    for job in range(offset,len(jobs)):
        _,q,s,fixed,edge,case_ids=jobs[job];variable=1-fixed
        candidate={key:(w,d,s if t==q else t)for key,(w,d,t)in table.items()if key[0]!=q}
        candidate[s,fixed]=edge
        if s in BOX_KERNEL and(s,variable)not in py.mutable_anchor_rows:
            w,d,t=table[s,variable];choices=[(w,d,s if t==q else t)]
        else:choices=[(w,d,t)for w in(0,1)for d in('L','R')for t in states+['254']if t!=q]
        oracle.engine.configure(candidate);affected=list(case_ids)
        for alternative in choices:
            trials+=1;candidate[s,variable]=alternative
            oracle.engine.set_edge((s,variable),alternative)
            for j,i in enumerate(affected):
                if not oracle.engine.run_case(oracle.cases[i]):
                    if j:affected.insert(0,affected.pop(j))
                    break
            else:
                body_passes+=1
                steps=fast_boot(candidate)
                if not py.check(candidate)[0]:raise ValueError('native/Python disagreement')
                if steps is None:
                    # Keep these distinct from accepted candidate-*.tm outputs.
                    # A different initial proof counter may admit a new proof.
                    pending=args.output/'body-only';pending.mkdir(exist_ok=True)
                    target=pending/f'body-{job}-{body_passes}.tm'
                    write_table(target,candidate)
                    recipe=dict(removed=q,survivor=s,fixed_branch=fixed,fixed_edge=edge,
                        synthesized_edge=alternative,states=len(candidate)//2,d0=args.d0,
                        python_instruction_cases=len(py.cases),bootstrap=bootstrap_root(candidate,args.d0))
                    save_json(target.with_suffix('.json'),recipe)
                    print('BODY_ONLY',target,recipe,flush=True)
                    continue
                # Both independent Python gates run before acceptance.
                if bootstrap(candidate)!=steps:raise ValueError('bootstrap checker disagreement')
                result=prune(candidate)
                if not py.check(result)[0] or bootstrap(result)!=steps:
                    raise ValueError('pruning changed the checked behavior')
                target=args.output/f'candidate-{len(result)//2}-{job}.tm'
                write_table(target,result)
                recipe=dict(removed=q,survivor=s,fixed_branch=fixed,fixed_edge=edge,
                    synthesized_edge=alternative,states=len(result)//2,bootstrap_steps=steps,d0=args.d0)
                save_json(target.with_suffix('.json'),recipe)
                print('FOUND',target,recipe,flush=True);return
        if job%10==0 or job+1==len(jobs):
            save_json(progress,dict(completed_jobs=job+1,total_jobs=len(jobs),trials=trials,
                body_passes=body_passes,seconds=time.monotonic()-began))
        if job%100==0 or job+1==len(jobs):
            print('job',job+1,'/',len(jobs),'trials',trials,'body_passes',body_passes,
                'seconds',round(time.monotonic()-began,1),flush=True)


if __name__=='__main__':main()
