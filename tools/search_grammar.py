"""Beam search jointly over source layout, inlining and instruction factoring."""
import argparse
from functools import partial
import json
import multiprocessing as mp
from pathlib import Path
import random
from machines import ROOT,count,totalize,write_table
from joint import build_joint,decode,encode
from search_joint import mutation
from reduce import reduce

PROBABILITIES=(None,0.,.25,.5,.75,1.)


def options(gene,preserve_main=False):
    kind,probability,seed=gene
    return {'kind':kind,'inline_probability':PROBABILITIES[probability],'seed':seed,'inline_main':not preserve_main}


def score(candidate,preserve_main=False,formula_choices=None):
    config,gene=candidate
    m=build_joint(config,sharing=True,grammar=options(gene,preserve_main),formula_choices=formula_choices)
    return len(reduce(totalize(m.tm.start,m.tm.states))),count(m.tm.states),candidate


def mutate(candidate,rng):
    config,(kind,p,seed)=candidate
    choice=rng.randrange(8)
    if choice<4:
        config=mutation(config,rng)
    elif choice==4:
        p=rng.randrange(len(PROBABILITIES))
    elif choice==5:
        kind=rng.choice(('random','cost'))
    else:
        seed=rng.randrange(2**24)
    return config,(kind,p,seed)


def run(args):
    initial_record=json.loads(args.initial.read_text())
    if initial_record.get('decoder') or initial_record.get('native') is not None:raise ValueError('allocated source: use search_native.py for native layouts, otherwise search_decoder.py')
    if initial_record.get("instruction_tree"):
        print("Source search rebuilds the saved source; run search_tree.py on its output to optimize the changed tree.",flush=True)
    formula_choices=initial_record.get("formula_choices")
    grammar=initial_record.get('grammar',{'kind':'random','inline_probability':.75,'seed':36})
    initial=(decode(initial_record),(grammar['kind'],PROBABILITIES.index(grammar['inline_probability']),grammar['seed']))
    if not initial[0][4]:raise ValueError('grammar search requires two-scratch source')
    preserve_main=args.preserve_main or not grammar.get("inline_main",True)
    evaluate=partial(score,preserve_main=preserve_main,formula_choices=formula_choices)
    champion=evaluate(initial);beam=[champion];seen={initial};rng=random.Random(args.seed)
    with mp.Pool(args.workers) as pool:
        for generation in range(args.generations):
            batch=set()
            while len(batch)<args.batch:
                c=mutate(rng.choice(beam)[2],rng)
                if c not in seen:batch.add(c)
            seen.update(batch)
            union=beam+pool.map(evaluate,sorted(batch))
            rng.shuffle(union);union.sort(key=lambda x:x[0]);beam=union[:args.width]
            if beam[0][0]<champion[0]:champion=beam[0]
            final,raw,(config,gene)=champion
            report={'kind':'ics-grammar','shared_operations':True, 'formula_choices':formula_choices, 'grammar':options(gene,preserve_main),
                    'seed':args.seed,'generations':generation+1,'width':args.width,'batch':args.batch,
                    'evaluations':len(seen),'raw_states':raw,'final_states':final,**encode(config)}
            args.output.parent.mkdir(parents=True,exist_ok=True)
            args.output.write_text(json.dumps(report,indent=2)+'\n')
            print(f'generation {generation+1}: {final}, frontier {beam[0][0]}..{beam[-1][0]}, {len(seen)} evaluated',flush=True)
    m=build_joint(config,sharing=True,grammar=options(gene,preserve_main),formula_choices=formula_choices)
    write_table(args.output.with_suffix('.tm'),m)


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--initial',type=Path,default=ROOT/'candidates/ics-best.json')
    p.add_argument('--seed',type=int,default=20260928)
    p.add_argument('--preserve-main',action='store_true')
    p.add_argument('--probe-grid',action='store_true',help='replay the 800-configuration initial grammar probe')
    p.add_argument('--width',type=int,default=96)
    p.add_argument('--batch',type=int,default=192)
    p.add_argument('--generations',type=int,default=60)
    p.add_argument('--workers',type=int,default=4)
    p.add_argument('--output',type=Path,default=ROOT/'scratch/ics-grammar.json')
    args=p.parse_args()
    if args.probe_grid:
        initial_record=json.loads(args.initial.read_text())
        if initial_record.get('decoder') or initial_record.get('native') is not None:raise ValueError('allocated source: use search_native.py for native layouts, otherwise search_decoder.py')
        if initial_record.get("instruction_tree"):
            print("Source search rebuilds the saved source; run search_tree.py on its output to optimize the changed tree.",flush=True)
        config=decode(initial_record)
        formula_choices=initial_record.get('formula_choices')
        tasks=[(config,(kind,PROBABILITIES.index(probability),seed))
               for kind in ('random','cost') for probability in (None,.25,.5,.75)
               for seed in range(100)]
        champion=None
        with mp.Pool(args.workers) as pool:
            for n,result in enumerate(pool.imap(partial(score,formula_choices=formula_choices),tasks),1):
                if champion is None or result[0]<champion[0]:champion=result
                if n%100==0:print(f'checked {n}: {champion[0]}',flush=True)
        final,raw,(config,gene)=champion
        report={'kind':'ics-grammar-probe','evaluations':len(tasks),'formula_choices':formula_choices,
                'raw_states':raw,'final_states':final,'shared_operations':True,
                'grammar':options(gene),**encode(config)}
        args.output.parent.mkdir(parents=True,exist_ok=True)
        args.output.write_text(json.dumps(report,indent=2)+'\n')
        write_table(args.output.with_suffix('.tm'),build_joint(config,sharing=True,grammar=options(gene),formula_choices=formula_choices))
    else:
        run(args)
