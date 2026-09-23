"""Independent arithmetic and literal-tape checks for fused unpair experiments."""
import random
from native import build_native
from machines import require
from register_check import compile_fragment,execute
from check_decoder import unpair,pair


def kernel_checks(record,cases=5000,seed=51097):
    from unpair_fusion import CANTOR_STEP
    m=build_native(record);rng=random.Random(seed)
    for line in CANTOR_STEP.splitlines():m.tm.loadline(line,'<Cantor step check>',0)
    for case in range(cases):
        values=[rng.randrange(50) for _ in range(rng.randrange(3,15))]
        values[1]=case%11
        expected=list(values);a,b=values[:2]
        expected[:2]=[a+1,b-1] if b else [0,a+1]
        gap=rng.randrange(2,20);bits='0'*gap
        for i in reversed(range(len(values))):
            if i<len(values)-1:bits+='00' if i==1 else '0'
            bits+='1'*(values[i]+1)
        ones={i for i,c in enumerate(bits) if c=='1'};head=0;q='1.cstep'
        for step in range(10000):
            if q=='6.break.0':break
            edge=m.tm.states.get((q,str(int(head in ones))))
            require(edge is not None,'Cantor kernel halted')
            w,d,q=edge
            if w=='1':ones.add(head)
            else:ones.discard(head)
            head+=1 if d=='R' else -1
        else:raise ValueError('Cantor kernel did not return')
        require(head==-1 and 0 not in ones,'Cantor return damaged IP')
        cells=sorted(ones);runs=[];last=None
        for pos in cells:
            if last is None or pos!=last+1:runs.append(1)
            else:runs[-1]+=1
            if last is not None:require(pos-last<=2,'Cantor kernel left an internal gap')
            last=pos
        require(list(reversed([n-1 for n in runs]))==expected,f'Cantor kernel values differ for {values}')
        require(cells[0]==gap+1,'Cantor kernel shifted wrong boundary')
    return {'kernel_cases':cases}


def arithmetic_checks(record,cases=2000):
    m=build_native(record,compile_machine=False)
    compiled=[compile_fragment(m,f(m.scratch1,m.scratch2,m.prooflist)) for f in (m.unpair,m.unpair_restore)]
    for n in range(cases):
        a,b=unpair(n)
        for restore,code in enumerate(compiled):
            initial={'prooflist':n,'param1':17,'topwff':9,'wffstack':11}
            after,_=execute(code,initial)
            expected={**initial,'prooflist':b if restore else 0,'scratch1':a,'scratch2':0 if restore else b}
            require(all(after.get(k,0)==expected.get(k,0) for k in set(after)|set(expected)),'fused unpair arithmetic differs')
    rng=random.Random(62881)
    for _ in range(256):
        x,y,n=rng.randrange(13),rng.randrange(13),rng.randrange(100)
        a,b=unpair(pair(x,y)+n)
        for restore,code in enumerate(compiled):
            initial={'scratch1':x,'scratch2':y,'prooflist':n,'param1':17}
            after,_=execute(code,initial)
            expected={**initial,'scratch1':a,'scratch2':0 if restore else b,'prooflist':b if restore else 0}
            require(all(after.get(k,0)==expected.get(k,0) for k in set(after)|set(expected)),'nonzero-output Cantor invariant differs')
    return {'unpair_cases':cases,'unpair_restore_cases':cases,'nonzero_output_cases':512}


def source_contract_check(record):
    from copy import deepcopy
    from unpair_fusion import build_contract
    from grammar import equivalent_cfg
    ref=deepcopy(record);ref['native'].pop('unpair')
    a=build_native(ref,compile_machine=False);b=build_contract(record)
    return equivalent_cfg(compile_fragment(a,a.main(),terminal='return'),
                          compile_fragment(b,b.main(),terminal='return'))


def direct_source_check(record):
    """A direct trace comparison is possible for the increment-first variants."""
    from copy import deepcopy
    from grammar import equivalent_cfg
    ref=deepcopy(record);ref['native'].pop('unpair')
    a=build_native(ref,compile_machine=False);b=build_native(record,compile_machine=False)
    try:
        return equivalent_cfg(compile_fragment(a,a.main(),terminal='return'),compile_fragment(b,b.main(),terminal='return'))
    except ValueError:
        require(record['native']['unpair']['variant'] in (1,2),'increment-first fusion changed the source trace')
        return None  # Decrement-first variants intentionally reorder operations.
