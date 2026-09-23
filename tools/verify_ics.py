"""Computational checks for the experimental ICS candidate; no Lean dependency."""
import argparse
import hashlib
import itertools
import json
from pathlib import Path
import re
from machines import ROOT,count,read_table,require,totalize
from ics import ICS,LOGICAL,RPN
from joint import PermutedICS,build_joint,decode,PERMUTATIONS,LOGIC_RPN
from storage import TwoScratchICS
from constructors import FusedICS
from encoding import ReversedFusion,ReversedTwoScratch
from register_check import compile_fragment,execute
from reduce import reduce,window_reads


def pair(a,b):
    return a+(a+b)*(a+b+1)//2


def formula_tree(tokens):
    """Parse constructor notation as a symbolic formula/variable expression."""
    stack=[]
    for token in tokens:
        if token.startswith('p'):
            stack.append(token)
        elif token=='wn':
            stack.append((token,stack.pop()))
        else:
            right=stack.pop();left=stack.pop()
            stack.append((token,left,right))
    require(len(stack)==1,'malformed constructor formula')
    return stack[0]


def source_checks():
    manifest=json.loads((ROOT/'reference/ics-upstream.json').read_text())
    for name,digest in manifest['files_sha256'].items():
        require(hashlib.sha256((ROOT/'vendor/cats'/name).read_bytes()).hexdigest()==digest,'ICS upstream file changed')
    text=(ROOT/'vendor/cats/zf2.nql').read_text()
    sections={'POW':('/* POW */','/* UNI */'),
              'UNI':('/* UNI */','/* UNI+POW */'),
              'ICS':('/* INF+COL+SEP */','/* B6a1 */'),
              'B6a1':('/* B6a1 */','/* B6a2 */'),
              'B6a2':('/* B6a2 */','/* GEN */')}
    for name,(begin,end) in sections.items():
        snippet=text.split(begin,1)[1].split(end,1)[0]
        active=re.sub(r'/\*.*?\*/','',snippet,flags=re.S)
        calls=re.findall(r'(\w+)\(\)\s*;',active)
        tokens=['p'+x[3:] if x.startswith('par') else x for x in calls if x!='select']
        require(tokens==RPN[name].split(),f'{name} differs from corrected upstream formula')
        formula_tree(tokens)
    # Check parameter-renaming round trips on every schema, independently of the builder.
    cases=0
    for source in list(LOGIC_RPN.values())+list(RPN.values()):
        original=formula_tree(source.split())
        for permutation in PERMUTATIONS:
            renamed=['p'+str(permutation[int(t[1:])-1]) if t.startswith('p') else t for t in source.split()]
            inverse={str(value):str(index+1) for index,value in enumerate(permutation)}
            restored=['p'+inverse[t[1:]] if t.startswith('p') else t for t in renamed]
            require(formula_tree(restored)==original,'schema renaming failed')
            cases+=1
    return {'published_constructor_sequences':5,'schema_renaming_cases':cases}


def arithmetic_checks():
    old=PermutedICS();new=TwoScratchICS()
    a=old.axioms();b=new.axioms()
    guard_old=compile_fragment(old,a[len(LOGICAL)][:2])
    guard_new=compile_fragment(new,b[len(LOGICAL)][:5])
    equal=lambda x,y:all(x.get(k,0)==y.get(k,0) for k in set(x)|set(y))
    guard_cases=0
    for x,y,z in itertools.product(range(5),repeat=3):
        for top,stack in ((0,0),(1,0),(0,2),(2,1)):
            initial={'param1':x,'param2':y,'param3':z,'topwff':top,'wffstack':stack}
            left,_=execute(guard_old,initial);right,_=execute(guard_new,initial)
            require(equal(left,right),'guard storage rewrite differs')
            require(right.get('topwff',0)==top and right.get('wffstack',0)==stack,'guard changes theorem stack')
            guard_cases+=1
    det_old=compile_fragment(old,a[0]);det_new=compile_fragment(new,b[0]);det_cases=0
    for minor,conclusion,valid in itertools.product(range(2),range(2),(False,True)):
        major=pair(pair(minor,conclusion),2)+(not valid)
        initial={'axiomcode':1,'param1':conclusion,'param2':2,'param3':1,
                 'topwff':0,'wffstack':pair(minor,pair(major,0))}
        left,_=execute(det_old,initial);right,_=execute(det_new,initial)
        require(equal(left,right),'selected detachment rewrite differs')
        require(right.get('topwff',0)==(conclusion if valid else 0),'incorrect detachment result')
        det_cases+=1
    for selector,p1,p2,p3,top in itertools.product((0,2),range(2),range(2),range(2),range(2)):
        initial={'axiomcode':selector,'param1':p1,'param2':p2,'param3':p3,'topwff':top}
        left,_=execute(det_old,initial);right,_=execute(det_new,initial)
        require(equal(left,right),'inactive detachment rewrite differs')
        det_cases+=1
    # Exercise selected detachment with a major premise in the new encoding.
    recoded=ReversedTwoScratch();recoded.tag_mode=1;recoded.binary_mode=0
    det_recoded=compile_fragment(recoded,recoded.axioms()[0])
    for minor,conclusion,valid in itertools.product(range(2),range(2),(False,True)):
        major=pair(pair(conclusion,minor),2)+(not valid)
        initial={'axiomcode':1,'param1':conclusion,'param2':2,'param3':1,
                 'topwff':0,'wffstack':pair(minor,pair(major,0))}
        result,_=execute(det_recoded,initial)
        require(result.get('topwff',0)==(conclusion if valid else 0),'recoded detachment result mismatch')
        require(result.get('wffstack',0)==0,'recoded detachment leaves a premise on the stack')
        require(result.get('scratch1',0)==result.get('scratch2',0)==0,'recoded detachment scratch not cleared')
        det_cases+=1
    constructor_cases=0
    for cls in (FusedICS,ReversedFusion):
        for fusion in range(8):
            for op,k in (('weq',0),('wel',1),('wim',2),('wn',3),('wal',4)):
                m=cls();m.tag_mode=fusion//2;m.binary_mode=fusion%2
                code=compile_fragment(m,getattr(m,op)())
                for left,top,tail in itertools.product(range(3),range(3),range(2)):
                    stack=pair(left,tail)
                    regs,_=execute(code,{'topwff':top,'wffstack':stack})
                    payload=top if op=='wn' else pair(top,left) if cls is ReversedFusion else pair(left,top)
                    require(regs.get('topwff',0)==pair(payload,k),'constructor encoding mismatch')
                    require(regs.get('wffstack',0)==(stack if op=='wn' else tail),'constructor damages stack tail')
                    require(regs.get('scratch1',0)==regs.get('scratch2',0)==0,'constructor scratch not cleared')
                    constructor_cases+=1
    return {'guard_cases':guard_cases,'detachment_cases':det_cases,'constructor_cases':constructor_cases}


def smoke(start,edges,steps):
    """Literal simulation, with observed gap at entry to a register primitive.

    The distance to the next 1 is diagnostic, not an unbounded tape invariant.
    No extrapolation from this finite run is made.
    """
    ones=set();head=0;q=start;dispatches=0;register_entries=0;minimum_gap=None
    for step in range(steps):
        dispatches+=q=='main().0'
        edge=edges.get((q,str(int(head in ones))))
        require(edge is not None,f'unexpected smoke-test halt at step {step}: {q}')
        w,d,target=edge
        if w=='1':ones.add(head)
        else:ones.discard(head)
        head+=1 if d=='R' else -1
        if q.startswith('3.') and target in ('1.inc','1.decnz','1.sel'):
            right=[p for p in ones if p>=head]
            require(bool(right),'register file absent in smoke test')
            gap=min(right)-head
            require(gap>=2,f'insufficient observed instruction/register gap: {gap}')
            minimum_gap=gap if minimum_gap is None else min(gap,minimum_gap)
            register_entries+=1
        q=target
    return {'steps':steps,'dispatches':dispatches,'register_entries':register_entries,
            'minimum_observed_gap':minimum_gap,'head':head,'state':q,'ones':len(ones)}


def verify(candidate=None,steps=1_000_000,windows=False,tree_boundaries=512):
    candidate=candidate or ROOT/'candidates/ics-best.json'
    result=json.loads(candidate.read_text())
    require(not result.get('native_addresses'),'use verify_native.py for exposed native addresses')
    require(hashlib.sha256(candidate.with_suffix('.tm').read_bytes()).hexdigest()==result['table_sha256'],'candidate table hash mismatch')
    config=decode(result)
    from instruction_tree import read_record
    tree=read_record(result,candidate.parent)
    m=build_joint(config,sharing=result.get("shared_operations",False),grammar=result.get("grammar"),formula_choices=result.get("formula_choices"),instruction_tree=tree,decoder=result.get('decoder'),native=result.get('native'))
    start,edges=read_table(candidate.with_suffix('.tm'))
    require(start==m.tm.start and edges==m.tm.states,'candidate does not rebuild exactly')
    require(count(edges)==result['raw_states'],'raw state count mismatch')
    final=reduce(totalize(start,edges))
    require(len(final)==result['final_states']==count(edges),'unexpected reduction: supply a certificate before promotion')
    names={q for q,b in edges}
    require(sum(q[0].isdigit() for q in names)==result['framework_states'],'framework count mismatch')
    require(sum(not q[0].isdigit() for q in names)==result['dag_states'],'DAG count mismatch')
    active={q.split('.')[1] for q in names if q.startswith('3.')}
    require(len(active)==result['active_registers'],'active register count mismatch')
    require(not any('scratch3' in q for q,b in edges),'third scratch register remains reachable')
    report={'status':'experimental; computational checks only','states':count(edges),
            'source':source_checks(),'arithmetic':arithmetic_checks(),'smoke':smoke(start,edges,steps)}
    if result.get("formula_choices"):
        from formula_rewrite import check_choices
        report["formula_rewrites"] = check_choices(result["formula_choices"])
    if result.get('decoder'):
        from check_decoder import check
        report['decoder']=check(result,cases=1000)
    if result.get('native') is not None:
        from check_native import kernel_checks,source_check,literal_check
        order=result['native']['register_order']
        directions=sorted({'movr' if order.index(a)>order.index(b) else 'movl' for a,b in result['native']['moves']})
        report['native']={'kernels':{d:kernel_checks(result,direction=d) for d in directions},
                          'expanded_source_cfg_pairs':source_check(result),
                          'literal_ir':literal_check(m,checks=1024)}
    if result.get("shared_operations"):
        from verify_sharing import sharing_checks
        report["shared_operations"]=sharing_checks(result)
    if result.get("grammar"):
        from verify_sharing import grammar_check
        report["grammar"]=grammar_check(result,None if tree is not None else m)
    if tree is not None:
        from verify_tree import tree_check
        report["instruction_tree"]=tree_check(result,m)
        if tree_boundaries:
            from tape_check import differential
            base=build_joint(config,sharing=result.get('shared_operations',False),
                             grammar=result.get('grammar'),formula_choices=result.get('formula_choices'),decoder=result.get('decoder'),native=result.get('native'))
            report['tape_differential']=differential(base,m,checks=tree_boundaries,limit=20_000_000)
    if windows:
        rows=totalize(start,edges);allowed={q:3 for q in rows};report['windows']=[]
        for left,right in ((3,3),(8,2),(2,8),(5,5),(10,2),(2,10),(6,6)):
            possible,n=window_reads(rows,left,right,allowed)
            allowed={q:allowed[q]&possible[q] for q in rows}
            report['windows'].append({'left':left,'right':right,'abstract_configurations':n,
                                      'allowed_state_reads':sum(mask.bit_count() for mask in allowed.values())})
    return report


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--candidate',type=Path)
    p.add_argument('--steps',type=int,default=1_000_000)
    p.add_argument('--windows',action='store_true')
    p.add_argument('--tree-boundaries',type=int,default=512,help='bounded tape comparisons at decrement entries; 0 disables')
    args=p.parse_args()
    require(args.steps>=0 and args.tree_boundaries>=0,'check limits must be nonnegative')
    print(json.dumps(verify(args.candidate,args.steps,args.windows,args.tree_boundaries),indent=2))
