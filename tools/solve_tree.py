"""Global binary-grammar optimization of closed instruction sequences.

Optional search dependency: OR-Tools. Verification and rebuilding use only the
standard library. Bounds apply to this finite grammar model, not to equivalent
Turing machines. A solver proposal is independently checked before saving.
"""
import argparse
from collections import Counter
from functools import lru_cache
import hashlib
import json
from pathlib import Path

from instruction_tree import Trees, read_record
from joint import build_joint, decode
from machines import ROOT, count, write_table, totalize
from reduce import reduce
from register_check import compile_fragment
from verify_tree import equivalent_increment_cfg


def canonical_words(tree, root, maximum_length=16):
    """Flatten only compositions of closed blocks; keep control nodes opaque."""
    atoms=[];lookup={};productions={}
    def atom(key):
        if key not in lookup:lookup[key]=len(atoms);atoms.append(key)
        return lookup[key]
    @lru_cache(None)
    def visit(v):
        if isinstance(v,str):return (atom(('leaf',v)),)
        a,b=tree.nodes[v];x,y=visit(a),visit(b)
        if tree.closed(a) and tree.closed(b):
            word=x+y;productions.setdefault(word,(x,y));return word
        return (atom(('node',x,y)),)
    rootword=visit(root);required={rootword}
    for a in atoms:
        if a[0]=='node':required.update(a[1:])
    required={w for w in required if len(w)>1}
    occurrences=Counter()
    for w in required:
        for size in range(2,min(maximum_length,len(w))+1):
            for start in range(len(w)-size+1):occurrences[w[start:start+size]]+=1
    words=set(productions)|required|{w for w,n in occurrences.items() if n>=2}
    for w in required:words.update(w[i:] for i in range(len(w)-1))
    return atoms,productions,required,rootword,sorted(words,key=lambda w:(len(w),w))


def materialize(atoms, productions, rootword):
    """Build a grammar DAG iteratively, including long right-associated words."""
    tree=Trees();done={};visiting=set();root=('word',rootword);stack=[(root,False)]
    def parts(key):
        kind,value=key
        if kind=='atom':
            a=atoms[value]
            return [] if a[0]=='leaf' else [('word',a[1]),('word',a[2])]
        if len(value)==1:return [('atom',value[0])]
        left,right=productions[value]
        if left+right!=value:raise ValueError('grammar production changes its word')
        return [('word',left),('word',right)]
    while stack:
        key,ready=stack.pop()
        if key in done:continue
        children=parts(key)
        if not ready:
            if key in visiting:raise ValueError('cyclic grammar')
            visiting.add(key);stack.append((key,True))
            stack.extend((child,False) for child in reversed(children))
            continue
        if not children:done[key]=atoms[key[1]][1]
        elif len(children)==1:done[key]=done[children[0]]
        else:done[key]=tree.node(*(done[child] for child in children))
        visiting.remove(key)
    return tree,done[root]


def run(args):
    from ortools.sat.python import cp_model
    record=json.loads(args.initial.read_text())
    source=build_joint(decode(record),sharing=record.get('shared_operations',False),
                       grammar=record.get('grammar'),formula_choices=record.get('formula_choices'),decoder=record.get('decoder'))
    original=compile_fragment(source,source.find_seq('main().0'),terminal='return')
    tree=Trees();source_root=tree.import_machine(source)
    backend=count(source.tm.states)-tree.size(source_root)
    data=read_record(record,args.initial.parent)
    root=tree.import_record(data,source.registers) if data else source_root
    incumbent=tree.size(root)+backend
    atoms,old,required,rootword,words=canonical_words(tree,root,args.max_word)
    idx={w:i for i,w in enumerate(words)}
    model=cp_model.CpModel()
    active=[model.new_bool_var('w'+str(i)) for i in range(len(words))]
    # This is a search-domain restriction, not a semantic limit of the backend.
    height=[model.new_int_var(0,30,'h'+str(i)) for i in range(len(words))]
    atomheight=[model.new_int_var(0,30,'a'+str(i)) for i in range(len(atoms))]
    maximum=model.new_int_var(2,args.max_zeros or 30,'maxzeros')
    for i,a in enumerate(atoms):
        if a[0]=='leaf':model.add(atomheight[i]==0)
        else:
            left=a[1];h=atomheight[left[0]] if len(left)==1 else height[idx[left]]
            model.add(atomheight[i]==h+1)
        model.add(maximum>=atomheight[i])
    for w in required:model.add(active[idx[w]]==1)
    choices=[];total=0
    for i,w in enumerate(words):
        options=[]
        for cut in range(1,len(w)):
            left,right=w[:cut],w[cut:]
            if any(len(x)>1 and x not in idx for x in (left,right)):continue
            e=model.new_bool_var(f'p{i}_{cut}');options.append((left,right,e));total+=1
            for child in (left,right):
                if len(child)>1:model.add_implication(e,active[idx[child]])
            h=atomheight[left[0]] if len(left)==1 else height[idx[left]]
            model.add(height[i]==h+1).only_enforce_if(e)
        model.add(sum(e for _,_,e in options)==active[i])
        model.add(maximum>=height[i]);model.add(height[i]==0).only_enforce_if(active[i].Not())
        model.add_hint(active[i],int(w in old))
        for left,right,e in options:model.add_hint(e,int(old.get(w)==(left,right)))
        choices.append(options)
    # Closed-word reassociation preserves the control/jump primitives.
    control=sum(a[0]=='node' for a in atoms)
    overhead=tree.size(root)-len(tree.reachable(root))-max(2,max(tree.zeros(v) for v in tree.reachable(root)))
    objective=sum(active)+maximum+control+overhead+backend
    if args.max_states is not None:model.add(objective<=args.max_states)
    model.minimize(objective)
    args.output.parent.mkdir(parents=True,exist_ok=True)
    solver=cp_model.CpSolver();solver.parameters.num_search_workers=args.workers
    solver.parameters.max_time_in_seconds=args.seconds;solver.parameters.max_memory_in_mb=4096
    best_actual=incumbent;artifact=None;proposals=0

    solutions=[]
    class Save(cp_model.CpSolverSolutionCallback):
        def on_solution_callback(self):
            productions={w:(left,right) for w,options in zip(words,choices)
                         for left,right,e in options if self.value(e)}
            solutions.append((productions,self.objective_value,self.best_objective_bound))
            print('model proposal',self.objective_value,'bound',self.best_objective_bound,flush=True)

    def inspect_solution(productions,objective_value,objective_bound):
        nonlocal best_actual,artifact,proposals
        proposed,root=materialize(atoms,productions,rootword)
        if proposed.size(root)+backend>incumbent:
            proposed.clear_caches()
            return
        m=build_joint(decode(record),compile_machine=False,decoder=record.get('decoder'))
        proposed.install(m,root);m.name_sequences();m.generate();m.tm.gc()
        pairs=equivalent_increment_cfg(original,compile_fragment(m,m.find_seq('main().0'),terminal='return'))
        raw=count(m.tm.states);final=len(reduce(totalize(m.tm.start,m.tm.states)));proposals+=1
        print('proposal',objective_value,'raw',raw,'reduced',final,'bound',objective_bound,flush=True)
        if raw<best_actual:
            best_actual=raw;artifact=args.output.with_name(args.output.stem+'-candidate.json')
            tp=artifact.with_suffix('.tree.json');tp.write_text(json.dumps(proposed.export(root),indent=2)+'\n')
            write_table(artifact.with_suffix('.tm'),m);names={q for q,b in m.tm.states}
            result={**record,'kind':'ics-global-instruction-tree','raw_states':raw,'final_states':final,
                    'framework_states':sum(q[0].isdigit() for q in names),'dag_states':sum(not q[0].isdigit() for q in names),
                    'instruction_tree':tp.name,'instruction_tree_sha256':hashlib.sha256(tp.read_bytes()).hexdigest(),
                    'table_sha256':hashlib.sha256(artifact.with_suffix('.tm').read_bytes()).hexdigest(),
                    'grammar_solver':{'matched_segment_pairs':pairs,'max_word':args.max_word,
                                      'model_objective':objective_value}}
            result.pop('tree_search',None)
            artifact.write_text(json.dumps(result,indent=2)+'\n')
        proposed.clear_caches()

    print('words',len(words),'binary productions',total,flush=True)
    status=solver.solve(model,Save())
    # Compile/check on the main thread, not a solver worker's small C stack.
    for proposal in solutions:inspect_solution(*proposal)
    result={'scope':'finite closed-word grammar model; not a Turing-machine lower bound',
            'status':solver.status_name(status),'seconds_limit':args.seconds,'workers':args.workers,
            'words':len(words),'productions':total,'solver_proposals':len(solutions),'checked_proposals':proposals,
            'model_bound':solver.best_objective_bound,'best_raw_states':best_actual,
            'target':args.max_states,'maximum_zero_run':args.max_zeros,'max_word':args.max_word,
            'artifact':str(artifact) if artifact else None}
    args.output.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result),flush=True)
    tree.clear_caches()


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--initial',type=Path,default=ROOT/'candidates/ics-best.json')
    p.add_argument('--output',type=Path,default=ROOT/'scratch/global-tree.json')
    p.add_argument('--seconds',type=float,default=180)
    p.add_argument('--workers',type=int,default=4)
    p.add_argument('--max-word',type=int,default=16)
    p.add_argument('--max-states',type=int)
    p.add_argument('--max-zeros',type=int)
    args=p.parse_args()
    if args.seconds<=0 or args.workers<1 or args.max_word<2 or (args.max_zeros is not None and not 2<=args.max_zeros<=30):
        p.error('invalid solver limits')
    run(args)
