"""Differential checks for shared arithmetic and an exact IR factoring audit."""
import itertools
from grammar import equivalent_cfg
from ics import LOGICAL
from joint import build_joint,decode
from machines import require
from register_check import compile_fragment,execute


def sharing_checks(record):
    config=decode(record)
    old=build_joint(config,compile_machine=False)
    new=build_joint(config,sharing=True,compile_machine=False)
    untouched={'prooflist':7,'nextproof':11,'param1':2,'param2':3,'param3':4}
    cases={}
    def compare(name, before, after, inputs):
        lhs=compile_fragment(old,before);rhs=compile_fragment(new,after)
        total=0
        for initial in inputs:
            start={**untouched,**initial}
            left,_=execute(lhs,start);right,_=execute(rhs,start)
            require(all(left.get(k,0)==right.get(k,0) for k in set(left)|set(right)),
                    f'{name} differs for {initial}: {left} != {right}')
            require(right.get('scratch1',0)==right.get('scratch2',0)==0,
                    f'{name} leaves nonzero scratch')
            total+=1
        cases[name]=total
    compare('push',old.pushwff(),new.pushwff(),
            ({'topwff':t,'wffstack':s} for t,s in itertools.product(range(20),range(40))))
    compare('select',old.select(),new.select(),
            ({'axiomcode':k,'topwff':t,'wffstack':s}
             for k,t,s in itertools.product(range(5),range(6),range(80))))
    for i in range(1,4):
        compare(f'parameter_{i}',getattr(old,f'par{i}')(),getattr(new,f'par{i}')(),
                ({f'param{i}':v,'topwff':t,'wffstack':s}
                 for v,t,s in itertools.product(range(9),range(4),range(5))))
    a=old.axioms();b=new.axioms();first=config[0][len(LOGICAL)]
    compare('protected_guard',a[first][:5],b[first][:6],
            ({'param1':x,'param2':y,'param3':z,'topwff':t,'wffstack':s}
             for x,y,z in itertools.product(range(5),repeat=3)
             for t,s in ((0,0),(1,0),(0,2),(2,1))))
    # Both changed low-level routines occur within selected/inactive detachment.
    def pair(a,b):return a+(a+b)*(a+b+1)//2
    selected=[]
    for minor,conclusion,valid in itertools.product(range(2),range(2),(False,True)):
        inner=pair(conclusion,minor) if config[5] else pair(minor,conclusion)
        major=pair(inner,2)+(not valid)
        selected.append({'axiomcode':1,'param1':conclusion,'param2':2,'param3':1,
                         'topwff':0,'wffstack':pair(minor,pair(major,0))})
    selected.extend({'axiomcode':k,'param1':p1,'param2':p2,'param3':p3,'topwff':top,'wffstack':0}
                    for k,p1,p2,p3,top in itertools.product((0,2),range(2),range(2),range(2),range(2)))
    compare('detachment',a[0],b[0],selected)
    return cases


def grammar_check(record,compiled=None):
    """Compare the complete source CFG with the factored CFG, for all branches.

    Falling through the main program is a distinct `return` exit. It must not
    be confused with the machine's explicit contradiction `halt` instruction.
    Unconditional jumps are hidden; every register op and both decrement
    outcomes must match. This is a finite graph check, not a Lean proof or a
    validation of the IR interpreter/tape backend.
    """
    config=decode(record);sharing=record.get('shared_operations',False)
    before=build_joint(config,sharing=sharing,compile_machine=False,formula_choices=record.get("formula_choices"))
    fragment=before.main()
    a=compile_fragment(before,fragment,terminal='return')
    after=compiled or build_joint(config,sharing=sharing,grammar=record.get('grammar'),formula_choices=record.get('formula_choices'))
    b=compile_fragment(after,after.find_seq('main().0'),terminal='return')
    pairs=equivalent_cfg(a,b)
    return {'source_cfg_nodes':len(a[1]),'compiled_cfg_nodes':len(b[1]),
            'matched_operation_pairs':pairs,'distinguishes_return_and_halt':True}
