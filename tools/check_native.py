"""Independent numerical and literal-tape contracts for native transfer trials."""
from collections import Counter
import random
from machines import require
from register_check import compile_fragment
from grammar import equivalent_cfg
from native import build_native


def kernel_checks(record,cases=2000,seed=901,direction="movr"):
    m=build_native(record);rng=random.Random(seed)
    # Restore unreferenced kernel rows for focused tests as well.
    from native import MOVE_RIGHT,MOVE_LEFT
    for line in (MOVE_RIGHT if direction=="movr" else MOVE_LEFT).splitlines():m.tm.loadline(line,'<native check>',0)
    for case in range(cases):
        length=rng.randrange(3,15);values=[rng.randrange(20) for _ in range(length)]
        source=rng.randrange(0 if direction=="movl" else 1,length-1);values[source]=case%21
        before=list(values);expected=list(values);expected[source+(-1 if direction=="movr" else 1)]+=expected[source];expected[source]=0
        gap=rng.randrange(2,20);bits='0'*gap
        for i in reversed(range(length)):
            if i<length-1:bits+='00' if i==source else '0'
            bits+='1'*(values[i]+1)
        ones={i for i,b in enumerate(bits) if b=='1'};head=0;q='1.'+direction
        for steps in range(10000):
            if q=='6.break.0':break
            edge=m.tm.states.get((q,str(int(head in ones))))
            require(edge is not None,'native kernel halted unexpectedly')
            w,d,q=edge
            if w=='1':ones.add(head)
            else:ones.discard(head)
            head+=1 if d=='R' else -1
        else:raise ValueError('native kernel did not return')
        require(head==-1 and 0 not in ones,'native return damaged IP boundary')
        cells=sorted(ones);runs=[];last=None
        for p in cells:
            if last is None or p!=last+1:runs.append(1)
            else:runs[-1]+=1
            if last is not None:require(p-last<=2,'native kernel left an internal tape gap')
            last=p
        require(list(reversed([n-1 for n in runs]))==expected,f'native values differ: {before}')
        require(cells[0]==gap+1,'unexpected native gap shift')
    return {'native_kernel_cases':cases}


def source_check(record):
    candidate=build_native(record)
    reference=build_native({**record,'native':None})
    return equivalent_cfg(compile_fragment(reference,reference.find_seq('main().0'),terminal='return'),
                          compile_fragment(candidate,candidate.find_seq('main().0'),terminal='return'))


def literal_check(machine,checks=512,limit=20000000):
    """Compare all registers to an independent atomic-IR execution at each op.

    The native kernel is checked separately. Whole-table execution must dispatch
    the expected register operation with exactly the expected input registers.
    One extra event validates the effects of the last requested operation.
    """
    pc,cfg=compile_fragment(machine,machine.find_seq('main().0'),terminal='return',expand_native=False)
    root=pc;expected={};ones=set();head=0;q=machine.tm.start;pending=None;done=0;gap_min=None;counts=Counter()
    active={op[1] for op in cfg.values() if op[0] in ('inc','decnz','movr','movl')}
    address_mode=getattr(machine,'native_addresses',False);selected=0
    declared=list(machine.registers);names=declared[:max(declared.index(x) for x in active)+1]
    moves={(a,op.split('.')[-1]):b for (a,b),op in getattr(machine,'native_opcodes',{}).items()}
    for step in range(limit):
        edge=machine.tm.states.get((q,str(int(head in ones))))
        require(edge is not None,'unexpected literal halt')
        w,d,target=edge
        if w=='1':ones.add(head)
        else:ones.discard(head)
        head+=1 if d=='R' else -1
        if not q[0].isdigit() and target.startswith('3.'):pending=target.split('.')[1:]
        address_call=address_mode and not q[0].isdigit()
        if address_call and target=='1.sel':selected+=1
        if (q.startswith('3.') or address_call) and target in ('1.inc','1.decnz','1.movr','1.movl'):
            if address_mode:
                require(0<selected<=len(names),'literal native selector index is invalid')
                reg,kind=names[selected-1],target.split('.')[1];selected=0
            else:
                require(pending is not None,'native dispatch lacks IR operation')
                reg,kind=pending
            seen=set()
            while cfg[pc][0] in ('goto','return'):
                require(pc not in seen,'silent IR cycle');seen.add(pc)
                pc=root if cfg[pc][0]=='return' else cfg[pc][1]
            op=cfg[pc]
            require(op[:2]==(kind,reg) and target=='1.'+kind,'literal operation differs from IR')
            cells=sorted(x for x in ones if x>=head);runs=[];last=None
            require(bool(cells) and cells[0]-head>=2,'missing register gap')
            gap_min=min(gap_min if gap_min is not None else 10**9,cells[0]-head)
            for x in cells:
                if last is None or x!=last+1:runs.append(1)
                else:runs[-1]+=1
                last=x
            require(len(runs)>=len(names),'truncated literal register file')
            actual=dict(zip(names,(n-1 for n in reversed(runs))))
            require(all(actual.get(k,0)==expected.get(k,0) for k in set(actual)|set(expected)),f'literal registers differ after {done} operations')
            if done==checks:return {'operations':done,'kinds':dict(counts),'steps':step+1,'compared_registers':len(names),'minimum_observed_gap':gap_min}
            value=expected.get(reg,0);pc=op[2]
            if kind=='inc':expected[reg]=value+1
            elif kind=='decnz':
                expected[reg]=max(0,value-1)
                if not value:pc=op[3]
            elif kind in ('movr','movl'):
                dest=moves[reg,kind];expected[dest]=expected.get(dest,0)+value;expected[reg]=0
            else:raise ValueError('unknown native operation')
            counts[kind]+=1;done+=1
        q=target
    raise ValueError('literal native check exceeded step budget')
