"""Exhaust all per-operator lowerings for a fixed source/layout configuration."""
import argparse
import itertools
import json
import multiprocessing as mp
from pathlib import Path
from machines import ROOT,count,totalize,write_table
from joint import decode,encode
from operators import build_operators
from reduce import reduce


def score(task):
    config,modes,mask,sharing,grammar,formula_choices=task
    m=build_operators(config,modes,mask,sharing=sharing,grammar=grammar,formula_choices=formula_choices)
    return len(reduce(totalize(m.tm.start,m.tm.states))),count(m.tm.states),modes


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--initial',type=Path,default=ROOT/'candidates/ics-best.json')
    p.add_argument('--mask',type=int,default=15)
    p.add_argument('--workers',type=int,default=4)
    p.add_argument('--output',type=Path,default=ROOT/'scratch/ics-operators.json')
    args=p.parse_args()
    initial=json.loads(args.initial.read_text())
    if initial.get('decoder') or initial.get('native') is not None:raise ValueError('allocated source: use search_native.py for native layouts, otherwise search_decoder.py')
    config=decode(initial);best=None
    if initial.get('instruction_tree'):print('Operator search rebuilds the source; run search_tree.py on its output.',flush=True)
    sharing=initial.get('shared_operations',False);grammar=initial.get('grammar');formula_choices=initial.get('formula_choices')
    tasks=((config,modes,args.mask,sharing,grammar,formula_choices) for modes in itertools.product(range(5),range(5),range(5),range(4),range(5)))
    with mp.Pool(args.workers) as pool:
        for n,result in enumerate(pool.imap(score,tasks),1):
            if best is None or result[0]<best[0]:
                best=result;print('best',best,flush=True)
            if n%250==0:print('evaluated',n,flush=True)
    m=build_operators(config,best[2],args.mask,sharing=sharing,grammar=grammar,formula_choices=formula_choices)
    report={'kind':'operator-lowerings','shared_operations':sharing,'grammar':grammar,'formula_choices':formula_choices,'evaluations':n,'initial':encode(config),'payload_mask':args.mask,
            'operator_modes':best[2],'raw_states':best[1],'final_states':best[0]}
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(report,indent=2)+'\n')
    write_table(args.output.with_suffix('.tm'),m)
