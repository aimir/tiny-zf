"""Independent CFG audit for an explicit instruction-tree artifact.

Consecutive increments commute. We compare their register-count multisets and
then the next decrement or exit, following both decrement outcomes. No rewrite
history or heuristic search rule is used in this audit.
"""
from collections import Counter
from functools import lru_cache


def equivalent_increment_cfg(a,b):
    def summarize(cfg):
        @lru_cache(None)
        def run(pc):
            counts=Counter();seen=set()
            while True:
                if pc in seen:
                    raise ValueError('increment/goto cycle is outside this checker')
                seen.add(pc);op=cfg[pc]
                if op[0]=='goto':pc=op[1]
                elif op[0]=='inc':
                    if op[2]!=op[3]:raise ValueError('increment has unequal successors')
                    counts[op[1]]+=1;pc=op[2]
                else:return tuple(sorted(counts.items())),op
        return run
    left,right=summarize(a[1]),summarize(b[1])
    pending=[(a[0],b[0])];seen=set()
    while pending:
        p,q=pending.pop()
        if (p,q) in seen:continue
        seen.add((p,q));xs,x=left(p);ys,y=right(q)
        if xs!=ys or x[:2]!=y[:2]:
            raise ValueError('different increment segment or branch/exit operation')
        if x[0] in ('halt','return'):continue
        if x[0]!='decnz':raise ValueError('unknown CFG operation')
        pending.extend(zip(x[2:],y[2:]))
    return len(seen)


def tree_check(record, compiled):
    from joint import build_joint,decode
    from register_check import compile_fragment
    source=build_joint(decode(record),sharing=record.get('shared_operations',False),
                       formula_choices=record.get('formula_choices'),compile_machine=False)
    a=compile_fragment(source,source.main(),terminal='return')
    b=compile_fragment(compiled,compiled.find_seq('main().0'),terminal='return')
    pairs=equivalent_increment_cfg(a,b)
    return {'source_cfg_nodes':len(a[1]),'compiled_cfg_nodes':len(b[1]),
            'matched_segment_pairs':pairs,'normalizes_increment_segments':True,
            'distinguishes_return_and_halt':True}
