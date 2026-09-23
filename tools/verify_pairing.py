"""Independent numerical contracts and finite backend checks for dyadic trials.

These checks do not prove preservation of the proof predicate or ZF independence.
Large dyadic formula/stack codes make complete numerical schema tests impractical.
"""
import argparse
import hashlib
import itertools
import json
from pathlib import Path

from machines import ROOT, count, read_table, require, totalize
from reduce import reduce
from pairing import build_pairing, KERNELS
from register_check import compile_fragment, execute
from instruction_tree import Trees, read_record
from grammar import equivalent_cfg
from verify_tree import equivalent_increment_cfg


def pair(a, b):
    return ((2*a+1) << b)-1


def unpair(n):
    positive=n+1
    b=(positive & -positive).bit_length()-1
    return (positive >> b)//2, b


def check_registers(actual, initial, updates):
    expected={**initial, **updates}
    require(all(actual.get(k,0)==expected.get(k,0) for k in set(actual)|set(expected)),
            f'register contract failed: got {actual}, expected {expected}')


def arithmetic_checks(record=None):
    record=record or json.loads((ROOT/'reference/pairing-experiments.json').read_text())['runs'][0]['initial']
    cases={'pair':0,'unpair':0,'constructors':0,'stack':0,'guard':0,'decoder':0,'detachment':0}
    sentinel={'nextproof':19,'axiomcode':7,'topwff':5,'wffstack':3,'param3':11,'scratch3':13}
    for kernel,inverse,dual in itertools.product(KERNELS,(False,True),(False,True)):
        m=build_pairing(record,kernel,positive_inverse=inverse,dual=dual,compile_machine=False)
        p=compile_fragment(m,m.pair(m.scratch1,m.param1,m.param2))
        u=compile_fragment(m,m.unpair(m.param1,m.param2,m.scratch1))
        for a,b in itertools.product(range(16),range(8)):
            # Bound the exponent, whichever logical argument carries it.
            if dual:a,b=b,a
            initial={**sentinel,'param1':a,'param2':b}
            values,_=execute(p,initial)
            check_registers(values,initial,{'param1':0,'param2':0,'scratch1':pair(b,a) if dual else pair(a,b)})
            cases['pair']+=1
        for n in range(1024):
            initial={**sentinel,'scratch1':n}
            values,_=execute(u,initial);a,b=unpair(n)
            require(pair(a,b)==n,'independent numeric round trip failed')
            if dual:a,b=b,a
            check_registers(values,initial,{'param1':a,'param2':b,'scratch1':0})
            cases['unpair']+=1

    # Cover all constructor lowerings and tag assignments, including both
    # payload directions. Small values keep the unary interpreter bounded.
    for tags,reverse,tag_order,dual in itertools.product(
            ('generic','alternating','repeat1','repeat2'), (False,True),
            itertools.permutations((2,3,4)),(False,True)):
        encode=lambda a,b:pair(b,a) if dual else pair(a,b)
        for fusion in (range(8) if tags=='generic' else (0,1)):
            r={**record,'fusion':fusion,'reverse_payload':reverse}
            m=build_pairing(r,tags=tags,tag_order=tag_order,dual=dual,compile_machine=False)
            for op,k in [('weq',0),('wel',1),('wim',tag_order[0]),('wn',tag_order[1]),('wal',tag_order[2])]:
                code=compile_fragment(m,getattr(m,op)())
                for left,top,tail in itertools.product(range(2),range(2),range(2)):
                    initial={'topwff':top,'wffstack':encode(left,tail),'nextproof':19,'param3':11}
                    values,_=execute(code,initial)
                    payload=(top if op=='wn' else encode(top,left) if reverse else encode(left,top))
                    check_registers(values,initial,{'topwff':pair(payload,k),
                        'wffstack':initial['wffstack'] if op=='wn' else tail})
                    cases['constructors']+=1

    # Check the composition interfaces that depend on the chosen encoding.
    dual=record.get('pairing',{}).get('dual',False)
    encode=lambda a,b:pair(b,a) if dual else pair(a,b)
    decode=lambda n:unpair(n)[::-1] if dual else unpair(n)
    m=build_pairing(record,compile_machine=False)
    push=compile_fragment(m,m.pushwff()); select=compile_fragment(m,m.select())
    for top,stack in itertools.product(range(4),range(7)):
        initial={'topwff':top,'wffstack':stack,'nextproof':17,'param2':9}
        values,_=execute(push,initial)
        check_registers(values,initial,{'topwff':0,'wffstack':encode(top,stack)})
        cases['stack']+=1
    for head,tail,selector,top in itertools.product(range(3),range(3),range(3),range(3)):
        initial={'topwff':top,'wffstack':encode(head,tail),'axiomcode':selector,'param2':9}
        values,_=execute(select,initial)
        check_registers(values,initial,{'topwff':head if selector==0 else top,
                                      'wffstack':tail,'axiomcode':max(0,selector-1)})
        cases['stack']+=1
    from ics import LOGICAL
    from joint import PERMUTATIONS
    clauses=m.axioms();guard_body=clauses[m.AXIOMORDER[len(LOGICAL)]]
    require(guard_body[0]==m.pushwff(),'protected guard boundary changed')
    guard=compile_fragment(m,guard_body[:6])
    p1,p2,p3=('param'+str(i) for i in PERMUTATIONS[m.protected_permutation])
    for a,b,c,top,stack in itertools.product(range(3),range(3),range(3),range(2),range(3)):
        initial={'param1':a,'param2':b,'param3':c,'topwff':top,'wffstack':stack,
                 'nextproof':17,'scratch3':9}
        values,_=execute(guard,initial)
        check_registers(values,initial,{p1:initial[p1]+int(initial[p1]==initial[p3]),
                                        p2:initial[p2]+int(initial[p2]==initial[p3])})
        cases['guard']+=1
    body=m.main()
    # First 17 entries contain enumeration and four destructive unpairs.
    # Assert the expected entry boundary instead of silently trusting a slice.
    require(body[17]==m.add_sequence(m.pushwff()),'main decoder boundary changed')
    decoder=compile_fragment(m,body[:17])
    for n in range(256):
        for pending in (0,n+1):
            initial={'prooflist':pending,'nextproof':n,'topwff':3,'wffstack':5,
                     'axiomcode':9,'param1':8,'param2':7,'param3':6}
            values,_=execute(decoder,initial)
            rest=pending-1 if pending else n
            updates={'nextproof':n if pending else n+1}
            for key in ('axiomcode','param1','param2','param3'):
                updates[key],rest=decode(rest)
            updates['prooflist']=rest
            check_registers(values,initial,updates);cases['decoder']+=1
    # Small selected DET cases: larger nested dyadic stacks quickly become
    # prohibitively large in unary. Conclusion and minor premise are both 0.
    det=compile_fragment(m,clauses[0])
    implication_tag=m.tag_order[0]
    for valid in (False,True):
        major=pair(encode(0,0),implication_tag)+int(not valid)
        encoded_stack=encode(0,encode(major,0))
        if encoded_stack>100_000:continue
        initial={'axiomcode':1,'param1':0,'param2':2,'param3':1,
                 'wffstack':encoded_stack}
        values,_=execute(det,initial)
        require(values.get('topwff',0)==0 and values.get('wffstack',0)==0,'small DET check failed')
        require(all(values.get('scratch'+str(i),0)==0 for i in (1,2,3)),'DET scratch not cleared')
        cases['detachment']+=1
    # Selector 2 leaves premise registers in place, enabling nonzero conclusions
    # without constructing an exponentially large two-premise stack. These are
    # local arithmetic states, not claims about reachable proof-search states.
    for minor,conclusion,valid in itertools.product(range(2),range(2),(False,True)):
        payload=encode(conclusion,minor) if record.get('reverse_payload',False) else encode(minor,conclusion)
        major=pair(payload,implication_tag)+int(not valid)
        initial={'axiomcode':2,'param1':conclusion,'param2':major,'param3':minor,
                 'wffstack':0}
        values,_=execute(det,initial)
        require(values.get('topwff',0)==(conclusion if valid else 0),'DET equality/acceptance mismatch')
        check_registers(values,initial,{'axiomcode':1,'wffstack':0,
                                      'topwff':conclusion if valid else 0})
        cases['detachment']+=1
    return cases


def verify(candidate, steps=1_000_000, boundaries=128):
    record=json.loads(candidate.read_text())
    require(record.get('kind')=='ics-dyadic-experiment','not a dyadic experiment')
    require(hashlib.sha256(candidate.with_suffix('.tm').read_bytes()).hexdigest()==record['table_sha256'],'table hash mismatch')
    base=build_pairing(record)
    plain=build_pairing({**record,'grammar':None},compile_machine=False);plain.main()
    source=compile_fragment(plain,plain.find_seq('main().0'),terminal='return')
    cfg=compile_fragment(base,base.find_seq('main().0'),terminal='return')
    factored_pairs=equivalent_cfg(source,cfg)
    tree=read_record(record,candidate.parent);machine=base
    tree_pairs=None
    if tree is not None:
        arena=Trees();root=arena.import_record(tree,base.registers)
        machine=build_pairing(record,compile_machine=False)
        arena.install(machine,root);machine.name_sequences();machine.generate();machine.tm.gc()
        tree_pairs=equivalent_increment_cfg(cfg,compile_fragment(machine,machine.find_seq('main().0'),terminal='return'))
        arena.clear_caches()
    start,edges=read_table(candidate.with_suffix('.tm'))
    require((start,edges)==(machine.tm.start,machine.tm.states),'table does not rebuild exactly')
    require(count(edges)==record['raw_states'],'raw state mismatch')
    require(len(reduce(totalize(start,edges)))==record['final_states'],'reduced state mismatch')
    from formula_rewrite import check_choices
    from verify_ics import smoke
    from tape_check import differential
    result={'status':'experimental; computational checks only',
            'arithmetic':arithmetic_checks(record),
            'formula_rewrites':check_choices(record.get('formula_choices',{})),
            'factored_cfg_pairs':factored_pairs,'tree_cfg_pairs':tree_pairs,
            'raw_states':count(edges),'final_states':record['final_states'],
            'smoke':smoke(start,edges,steps)}
    if boundaries:
        result['tape_differential']=differential(base,machine,checks=boundaries,limit=20_000_000)
    return result


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--candidate',type=Path)
    p.add_argument('--steps',type=int,default=1_000_000)
    p.add_argument('--boundaries',type=int,default=128)
    args=p.parse_args()
    if min(args.steps,args.boundaries)<0:p.error('negative check bound')
    print(json.dumps(verify(args.candidate,args.steps,args.boundaries) if args.candidate else arithmetic_checks(),indent=2))
