"""Search instruction trees, screening exact raw sizes before full reduction.

A saved tree can seed another run. Source formulas, lowering and native register
kernels stay fixed. Every saved improvement passes the independent CFG audit.
Interning arenas are compacted each generation to bound memory use.
"""
import argparse
import hashlib
import json
from pathlib import Path
import random

from instruction_tree import Trees, read_record
from joint import build_joint, decode
from machines import ROOT, count, totalize, write_table
from reduce import reduce
from register_check import compile_fragment
from verify_tree import equivalent_increment_cfg


def run(args):
    record=json.loads(args.initial.read_text())
    source=build_joint(decode(record),sharing=record.get('shared_operations',False),
                       grammar=record.get('grammar'),formula_choices=record.get('formula_choices'))
    original=compile_fragment(source,source.find_seq('main().0'),terminal='return')
    tree=Trees(args.mode,not args.no_commute,args.break_floor)
    source_root=tree.import_machine(source)
    fixed=count(source.tm.states)-tree.size(source_root)
    initial_tree=read_record(record,args.initial.parent)
    root=tree.import_record(initial_tree,source.registers) if initial_tree else source_root
    rng=random.Random(args.seed)
    args.output.parent.mkdir(parents=True,exist_ok=True)

    def compile_tree(arena,root):
        m=build_joint(decode(record),compile_machine=False)
        arena.install(m,root);m.name_sequences();m.generate();m.tm.gc()
        return m

    def inspect(arena,root):
        m=compile_tree(arena,root)
        pairs=equivalent_increment_cfg(original,compile_fragment(m,m.find_seq('main().0'),terminal='return'))
        raw=count(m.tm.states)
        # A floor of two is retained only to reproduce the first search runs.
        if args.break_floor==1 and raw!=arena.size(root)+fixed:
            raise ValueError('raw state-count model disagrees with emitted table')
        return len(reduce(totalize(m.tm.start,m.tm.states))),raw,m,pairs

    def save(arena,root,generation,checked):
        final,raw,m,pairs=checked
        data=arena.export(root);path=args.output.with_suffix('.tree.json')
        path.write_text(json.dumps(data,indent=2)+'\n')
        write_table(args.output.with_suffix('.tm'),m)
        names={q for q,b in m.tm.states}
        result={**record,'kind':'ics-instruction-tree','raw_states':raw,'final_states':final,
                'framework_states':sum(q[0].isdigit() for q in names),
                'dag_states':sum(not q[0].isdigit() for q in names),
                'instruction_tree':path.name,'instruction_tree_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),
                'table_sha256':hashlib.sha256(args.output.with_suffix('.tm').read_bytes()).hexdigest(),
                'tree_search':{'seed':args.seed,'generations':generation,'batch':args.batch,
                               'width':args.width,'mode':args.mode,'commute':not args.no_commute,
                               'stratified':args.stratified,'edge_rewrites':args.edge_rewrites,
                               'break_floor':args.break_floor,'screen':args.screen,
                               'mutation_attempts':generation*args.batch,
                               'matched_segment_pairs':pairs}}
        args.output.write_text(json.dumps(result,indent=2)+'\n')

    best=root;checked=inspect(tree,root);best_score=checked[:2]
    save(tree,best,0,checked)
    beam=[root];raw_champion=tree.size(root)
    for generation in range(args.generations):
        trial=set(beam)
        for _ in range(args.batch):
            current=rng.choice(beam)
            for _ in range(1 if rng.randrange(4) else rng.randrange(2,5)):
                possible=[(v,w) for v in tree.reachable(current) for w in tree.rotations(v)]
                if not possible:break
                v,w=rng.choice(possible)
                if args.edge_rewrites and rng.randrange(4)==0:
                    parents=[p for p in tree.reachable(current) if v in tree.nodes[p]]
                    if parents:
                        parent=rng.choice(parents);a,b=tree.nodes[parent]
                        w=tree.node(w if a==v else a,w if b==v else b);v=parent
                current=tree.replace(current,v,w)
            trial.add(current)
        scored=[(tree.size(v),v) for v in trial]
        rng.shuffle(scored);scored.sort(key=lambda x:x[0])
        if args.stratified:
            beam=[]
            quotas=(args.width*2//5,args.width*3//10,args.width-args.width*7//10)
            for offset,quota in enumerate(quotas):
                beam.extend([v for s,v in scored if s==scored[0][0]+offset][:quota])
            floor=args.width*4//5
            if len(beam)<floor:
                beam.extend(v for _,v in scored if v not in beam and len(beam)<floor)
        else:beam=[v for _,v in scored[:args.width]]
        inspect_roots=[v for _,v in scored[:args.screen]]
        if scored[0][0]<raw_champion:
            raw_champion=scored[0][0]
            if scored[0][1] not in inspect_roots:inspect_roots.append(scored[0][1])
        for candidate in inspect_roots:
            result=inspect(tree,candidate)
            if result[:2]<best_score:
                best_score=result[:2];best=candidate;save(tree,best,generation+1,result)
                print('improved',generation+1,*best_score,flush=True)
        if (generation+1)%10==0:
            print('generation',generation+1,'best',best_score[0],
                  'frontier',scored[0][0]+fixed,max(tree.size(v) for v in beam)+fixed,flush=True)
        old=tree;tree,roots=old.compact([best,*beam]);best,*beam=roots;old.clear_caches()
    # Full reduction of every retained final candidate, not just the raw champion.
    for candidate in beam:
        result=inspect(tree,candidate)
        if result[:2]<best_score:best_score=result[:2];best=candidate
    save(tree,best,args.generations,inspect(tree,best))
    print('result',args.output,'states',best_score[0],flush=True)
    tree.clear_caches()


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--initial',type=Path,default=ROOT/'candidates/ics-best.json')
    p.add_argument('--output',type=Path,default=ROOT/'scratch/tree-search.json')
    p.add_argument('--seed',type=int,default=20261009)
    p.add_argument('--generations',type=int,default=300)
    p.add_argument('--batch',type=int,default=256)
    p.add_argument('--width',type=int,default=80)
    p.add_argument('--mode',choices=('basic','continue','general'),default='general')
    p.add_argument('--no-commute',action='store_true')
    p.add_argument('--stratified',action='store_true')
    p.add_argument('--edge-rewrites',action='store_true')
    p.add_argument('--break-floor',type=int,choices=(1,2),default=1,
                   help='2 reproduces the first runs; 1 scores the exact jump-state requirement')
    p.add_argument('--screen',type=int,default=4,help='fully reduce this many raw leaders per generation')
    args=p.parse_args()
    if min(args.generations,args.batch,args.width)<1 or args.screen<0:p.error('invalid search sizes')
    run(args)
