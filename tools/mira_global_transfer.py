"""Revalidate and extend semantic edge menus across a beam of native tables.

This quick screen is deliberately incomplete: it fully learns changed states
and new transition targets, retaining only rechecked old alternatives elsewhere.
Any quotient still needs full instruction, bootstrap, and Coq validation.
"""
import argparse,json
from pathlib import Path
from instruction_tree import Trees
from mira_global import Oracle,BOX_KERNEL,state_key,save_json,checkpoint_identity,bootstrap


def read(path):
    result={}
    for line in Path(path).read_text().splitlines():
        if not line or line.startswith('#'):continue
        q,b,w,d,t=line.split();result[q,int(b)]=int(w),d,t
    return result


def transfer(upstream,base_table,base_options,table_path,tree_path,folder,native=None):
    table=read(table_path);base=read(base_table)
    data=json.loads(Path(tree_path).read_text());tr=Trees()
    for i,pair in enumerate(data['nodes']):
        if tr.node(*pair)!=i:raise ValueError('duplicate tree node')
    oracle=Oracle(upstream,tr,data['root'],table)
    oracle.protected=BOX_KERNEL
    oracle.mutable_anchor_rows=frozenset([('3',0),('6',0),('48',0),('69',1)])
    if native:
        from mira_global_native import NativeOracle
        oracle=NativeOracle(oracle,native)
    folder.mkdir(parents=True,exist_ok=True);checkpoint_identity(oracle,folder)
    old=json.loads(Path(base_options).read_text())
    options=json.loads((folder/'options.json').read_text()) if (folder/'options.json').exists() else {}
    states=sorted({q for q,b in table},key=state_key);oldstates={q for q,b in base}
    targets=set(states)|{'254'};new=targets-oldstates-{'254'}
    altered={q for q in states if any(table[q,b]!=base.get((q,b)) for b in(0,1))}
    full=[(w,d,t)for w in(0,1)for d in('L','R')for t in states+['254']]
    added=[(w,d,t)for w in(0,1)for d in('L','R')for t in new]
    print('transfer',Path(table_path).stem,'changed states',sorted(altered),'new targets',sorted(new),flush=True)
    for q in states:
        for b in(0,1):
            key=f'{q}:{b}'
            if key in options:continue
            if q in oracle.protected and(q,b)not in oracle.mutable_anchor_rows:
                options[key]=[table[q,b]]
            else:
                trials=full if q in altered else [tuple(e)for e in old.get(key,[])if e[2]in targets]+added+[table[q,b]]
                choices=[]
                for e in dict.fromkeys(trials):
                    if e==table[q,b] or oracle.check_edge((q,b),e):choices.append(e)
                options[key]=choices
            save_json(folder/'options.json',options)
    # Prioritize choices which work on the exact unchanged blank-tape fixture.
    for q,b in [('5',1),('8',0),('8',1)]:
        if (q,b)not in table:continue
        key=f'{q}:{b}';choices=[];original=table[q,b]
        for raw in options[key]:
            e=tuple(raw);table[q,b]=e
            if e==original or bootstrap(table) is not None:choices.append(e)
        table[q,b]=original;options[key]=choices
    save_json(folder/'options-boot-filtered.json',options)
    save_json(folder/'transfer.json',dict(base_table=str(base_table),base_options=str(base_options),table=str(table_path),tree=str(tree_path),changed_states=sorted(altered),new_targets=sorted(new),edge_trials=oracle.trials,rows=len(options)))
    print('finished',Path(table_path).stem,oracle.trials,'edge trials',flush=True)


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--upstream',type=Path,required=True);p.add_argument('--base-table',type=Path,required=True)
    p.add_argument('--base-options',type=Path,required=True);p.add_argument('--table',type=Path,required=True)
    p.add_argument('--tree',type=Path,required=True);p.add_argument('--output',type=Path,required=True)
    p.add_argument('--native',type=Path)
    a=p.parse_args();transfer(a.upstream,a.base_table,a.base_options,a.table,a.tree,a.output,a.native)


if __name__=='__main__':main()
