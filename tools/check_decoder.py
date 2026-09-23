"""Independent boundary checks for decoder and packed-counter experiments."""
from math import isqrt
import json
import random
from pathlib import Path

from decoder import FIELDS, allocation_plan, build_decoder
from machines import ROOT,require
from register_check import compile_fragment,execute
from joint import build_joint,decode
from grammar import equivalent_cfg


def pair(a,b):return a+(a+b)*(a+b+1)//2


def unpair(n):
    s=(isqrt(8*n+1)-1)//2
    a=n-s*(s+1)//2
    return a,s-a


def check_plan(options):
    """Audit generated moves with distinct symbolic live-value tokens.

    This does not execute the planner's state machine. Each split must consume
    the next tail token into two zero registers; destructive transfers move
    one token, and clears may only discard old field values. It then checks
    the declared external assignment and exactly four splits.
    """
    state={k:('old',k) for k in FIELDS}
    state.update(prooflist=('tail',0),scratch1=None,scratch2=None)
    splits=0
    for op in allocation_plan(options):
        if op[0]=='clear':
            r=op[1];require(state[r] is None or state[r][0]=='old','clear destroys a live token');state[r]=None
        elif op[0]=='move':
            a,b=op[1:];require(a!=b and state[b] is None,'transfer destination is occupied')
            state[b]=state[a];state[a]=None
        elif op[0]=='unpair':
            a,b,n=op[1:]
            require(len({a,b,n})==3 and state[a] is None and state[b] is None,'bad split destinations')
            require(state[n]==('tail',splits),'split wrong proof tail')
            state[n]=None;state[a]=('field',splits);splits+=1;state[b]=('tail',splits)
        else:raise ValueError('unknown plan operation')
    require(splits==4,'wrong number of splits')
    for i,name in enumerate(options.get('order',FIELDS)):
        require(state[name]==('field',i),'wrong field assignment')
    require(state['prooflist']==('tail',4) and state['scratch1'] is None and state['scratch2'] is None,'wrong decoder boundary')
    return len(allocation_plan(options))


def check(record, cases=100, seed=8103):
    options=record['decoder'];check_plan(options)
    m=build_decoder({**record,'grammar':None},compile_machine=False);m.main()
    first,middle,suffix=m.decoder_sections
    packed=options.get('packed_counter',False);borrow=options.get('borrow_stack',False)
    start=[first,middle]
    # Compare at the boundary after the original default-theorem push.
    if not(packed or borrow):start.append(m.v_0())
    code=compile_fragment(m,start)
    ref=build_joint(decode(record),sharing=record.get('shared_operations',False),
                    formula_choices=record.get('formula_choices'),compile_machine=False)
    original=ref.main()
    # Original main has enum + four clears + twelve split/move entries, then
    # its default push. Everything after that boundary must be unchanged.
    require(original[17]==ref.add_sequence(ref.v_0()),'reference boundary changed')
    if not(packed or borrow):suffix=suffix[1:]
    matched=equivalent_cfg(compile_fragment(ref,original[18:],terminal='return'),
                           compile_fragment(m,suffix,terminal='return'))
    rng=random.Random(seed)
    for i in range(cases):
        proof=(0 if i%5==0 else rng.randrange(1,64 if packed else 2000))
        counter=rng.randrange(12)
        top,stack=rng.randrange(4),rng.randrange(4)
        initial={'prooflist':pair(counter,proof) if packed else proof,
                 'topwff':top,'wffstack':stack,'scratch3':7,
                 **{f:rng.randrange(20) for f in FIELDS}}
        if not packed:initial['nextproof']=counter
        after,_=execute(code,initial)
        n=proof-1 if proof else counter
        expected={**initial,'topwff':0,'wffstack':pair(top,stack)}
        for f in options.get('order',FIELDS):expected[f],n=unpair(n)
        nextcounter=counter+int(proof==0)
        expected['prooflist']=pair(nextcounter,n) if packed else n
        if not packed:expected['nextproof']=nextcounter
        require(all(after.get(k,0)==expected.get(k,0) for k in set(after)|set(expected)),
                f'decoder boundary differs: {options}, input={initial}, got={after}, want={expected}')
    return {'boundary_cases':cases,'unchanged_body_cfg_pairs':matched,'symbolic_plan_operations':check_plan(options)}


if __name__=='__main__':
    from search_decoder import grid,mutate_allocation
    base=json.loads((ROOT/'candidates/ics-best.json').read_text())
    records=list(grid(base));rng=random.Random(48013)
    sampled=rng.sample(records,32)
    checked=0;plans=0
    for record in records:
        try:check_plan(record['decoder']);plans+=1
        except ValueError:pass
    for record in sampled:
        for packed,borrow in ((False,False),(True,False),(False,True)):
            r={**record,'decoder':{**record['decoder'],'packed_counter':packed,'borrow_stack':borrow}}
            try:check_plan(r['decoder'])
            except ValueError:continue
            check(r,50);checked+=50
    print(json.dumps({'valid_grid_plans_audited':plans,'numerical_boundary_cases':checked}))
