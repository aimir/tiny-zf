"""Repack native transfer chains without discarding a checked instruction tree.

For each orientation, a subset dynamic program minimizes the number of register
selector states. Finalists still receive complete table reduction and CFG checks.
"""
import argparse
from copy import deepcopy
from functools import lru_cache
import json
from pathlib import Path
from types import SimpleNamespace

from machines import require
from native import build_native
import search_pairing as engine


def placements(record, tree, width=4):
    require(not (record.get('native') or {}).get('unpair'),'use search_unpair.py to preserve fused arithmetic')
    machine=build_native(record,compile_machine=False)
    leaves={x for pair in tree['nodes'] for x in pair if isinstance(x,str)}
    pairs=[p for p,op in machine.native_opcodes.items() if op in leaves]
    if not pairs:return []
    successor=dict(pairs);predecessor={b:a for a,b in pairs}
    require(len(successor)==len(pairs)==len(predecessor),'native transfers must form disjoint chains')
    names=list(machine.registers)[:-1];blocks=[];visited=set()
    for name in names:
        if name in predecessor:continue
        block=[name]
        while block[-1] in successor:block.append(successor[block[-1]])
        blocks.append(block);visited.update(block)
    require(visited==set(names),'cyclic native transfer graph')
    result=[]
    for direction in ('movl','movr'):
        oriented=[b if direction=='movl' else b[::-1] for b in blocks]
        uses={kind:{x.split('.')[1] for x in leaves if x.startswith('3.') and x.endswith('.'+kind)} for kind in ('inc','decnz')}
        uses[direction]={a for a,b in pairs}
        masks={kind:sum(1<<i for i,b in enumerate(oriented) if set(b)&regs) for kind,regs in uses.items()}
        all_mask=(1<<len(blocks))-1
        @lru_cache(None)
        def best(mask):
            if not mask:return [(0,())]
            length=sum(len(b) for i,b in enumerate(oriented) if mask>>i&1)
            candidates=[]
            for i,b in enumerate(oriented):
                if not mask>>i&1:continue
                previous=mask^(1<<i);cost=0
                for kind,regs in uses.items():
                    needed=masks[kind]
                    if needed and mask&needed==needed and previous&needed!=needed:
                        cost+=length-len(b)+max(j for j,r in enumerate(b) if r in regs)+1
                candidates.extend((score+cost,path+(i,)) for score,path in best(previous))
            return sorted(candidates)[:width]
        for selector_states,path in best(all_mask):
            order=[r for i in path for r in oriented[i]]+['scratch3']
            new_record=deepcopy(record)
            new_record['native']={'register_order':order,'moves':[list(p) for p in pairs]}
            replacement={machine.native_opcodes[a,b]:f'3.{a}.{direction}' for a,b in pairs}
            new_tree={**tree,'nodes':[[replacement.get(x,x) if isinstance(x,str) else x for x in pair] for pair in tree['nodes']]}
            result.append((new_record,new_tree,selector_states,direction))
    return result


def run(args):
    rows=[r for path in args.frontiers for r in json.loads(path.read_text()) if r.get('tree')]
    settings=SimpleNamespace(tree_generations=0,tree_batch=1,tree_width=1,tree_screen=0,memory_mb=512)
    seen=set();results=[];best=None
    for index,row in enumerate(rows):
        for record,tree,selectors,direction in placements(row['record'],row['tree'],args.width):
            key=json.dumps((record,tree),sort_keys=True)
            if key in seen:continue
            seen.add(key)
            source=engine.inspect_source(record,builder=build_native)
            result=engine.tree_search({**source,'tree':tree},{},settings,0,builder=build_native)
            result.update(input_index=index,direction=direction,selector_states=selectors)
            results.append(result)
            if best is None or (result['final_states'],result['raw_states'])<(best['final_states'],best['raw_states']):
                best=result
                engine.save(args.output,best,best['tree'],builder=build_native,kind='ics-native-placement-experiment')
                print('placement',len(results),'input',index,'direction',direction,'final',best['final_states'],flush=True)
    require(bool(results),'no emitted native operations in the supplied trees')
    report={'inputs':len(rows),'placement_evaluations':len(results),'best_states':best['final_states'],
            'best_by_direction':{d:min(r['final_states'] for r in results if r['direction']==d) for d in ('movl','movr')},
            'finalists':[{k:v for k,v in r.items() if k!='tree'} for r in results]}
    args.output.with_suffix('.report.json').write_text(json.dumps(report,indent=2)+'\n')
    print('placement result',report['best_states'],report['best_by_direction'],flush=True)


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('frontiers',nargs='+',type=Path)
    p.add_argument('--output',type=Path,default=Path('scratch/native-placement.json'))
    p.add_argument('--width',type=int,default=4)
    args=p.parse_args()
    if args.width<1:p.error('width must be positive')
    args.output.parent.mkdir(parents=True,exist_ok=True)
    run(args)
