"""Bounded literal-tape differential check at source decrement boundaries."""
from collections import Counter
from machines import require


def boundaries(machine, register_names, limit):
    ones=set();head=0;q=machine.tm.start;pending=None;increments=Counter()
    minimum_gap=None
    for step in range(limit):
        edge=machine.tm.states.get((q,str(int(head in ones))))
        require(edge is not None,'unexpected halt during tape differential check')
        write,direction,target=edge
        if write=='1':ones.add(head)
        else:ones.discard(head)
        head+=1 if direction=='R' else -1
        if not q[0].isdigit() and target.startswith('3.'):
            pending=target.split('.')[1:]
        if q.startswith('3.') and target in ('1.inc','1.decnz'):
            require(pending is not None,'register primitive without a source instruction')
            register,operation=pending
            require(target=='1.'+operation,'source/backend operation mismatch')
            if operation=='inc':increments[register]+=1
            else:
                cells=sorted(p for p in ones if p>=head)
                require(bool(cells),'missing register file')
                gap=cells[0]-head
                require(gap>=2,'insufficient observed instruction/register separation')
                minimum_gap=gap if minimum_gap is None else min(minimum_gap,gap)
                runs=[];last=None
                for cell in cells:
                    if last is None or cell!=last+1:runs.append(1)
                    else:runs[-1]+=1
                    last=cell
                require(len(runs)>=len(register_names),'truncated register file')
                # Declaration index 0 is the rightmost unary register.
                values=dict(zip(register_names,(n-1 for n in reversed(runs))))
                yield {'register':register,'increments':dict(increments),'values':values,
                       'steps':step+1,'minimum_observed_gap':minimum_gap}
                increments.clear()
        q=target
    raise ValueError('tape differential check exceeded its step budget')


def differential(source,candidate,checks=64,limit=10_000_000):
    require(checks>0 and limit>0,'differential limits must be positive')
    active={q.split('.')[1] for q,b in source.tm.states if q.startswith('3.')}
    declared=list(source.registers)
    names=declared[:max(declared.index(r) for r in active)+1]
    a=boundaries(source,names,limit);b=boundaries(candidate,names,limit)
    increments=0
    for _ in range(checks):
        x,y=next(a),next(b)
        for key in ('register','increments','values'):
            require(x[key]==y[key],f'tape differential mismatch in {key}')
        increments+=sum(x['increments'].values())
    return {'decrement_boundaries':checks,'increments_between_boundaries':increments,
            'compared_registers':len(names),'source_steps':x['steps'],'candidate_steps':y['steps'],
            'source_minimum_observed_gap':x['minimum_observed_gap'],
            'candidate_minimum_observed_gap':y['minimum_observed_gap']}
