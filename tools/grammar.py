"""Experimental straight-line inlining and global instruction-tree factoring."""
import random
from functools import lru_cache


def context_requirements(machine):
    """Return a memoized zero/one ancestor requirement for every IR subtree."""
    old=machine.sequences
    @lru_cache(None)
    def required_context(v):
        # A break needs k+1 enclosing left edges; a continue needs k
        # enclosing right edges. Natural completion needs one left edge.
        if isinstance(v,str):
            if v=='halt':return (0,0)
            if v.endswith(('.inc','.movr','.movl')):return (1,0)
            if v.endswith('.decnz'):return (2,0)
            kind,level=v[1:].split('.')
            return (int(level)+1,0) if kind=='break' else (0,int(level))
        values=[required_context(x) for x in old[v].seq]
        z,o=values[-1]
        for left_z,left_o in reversed(values[:-1]):
            z=max(left_z-1,z,0)
            o=max(left_o,o-1,0)
        return z,o
    return required_context


def inline_closed(machine, probability=1., seed=0, inline_main=True):
    """Inline only sequences of blocks whose jumps remain inside each block.

    A closed block needs at most its normal return edge from the caller and no
    enclosing continue target. Both parent and child must be straight-line
    compositions of such blocks. Control-containing loop/conditional nodes
    remain opaque. The final CFG audit is an independent safeguard.
    """
    old=machine.sequences
    rng=random.Random(seed)
    required_context=context_requirements(machine)
    def closed(v):
        zeros,ones=required_context(v)
        return zeros<=1 and ones==0
    expand={i for i,s in enumerate(old) if all(closed(v) for v in s.seq) and rng.random()<probability}
    if not inline_main:
        expand.discard(machine.find_seq("main().0"))
    @lru_cache(None)
    def flattened(i):
        out=[]
        for v in old[i].seq:
            if isinstance(v,int) and v in expand and i in expand:
                out.extend(flattened(v))
            else:
                out.append(flattened(v) if isinstance(v,int) else v)
        return tuple(out)
    root=flattened(machine.find_seq('main().0'))
    machine.sequences=[];machine.sequence_lookup={};machine.memo={}
    index=machine.add_sequence(root)
    machine.sequences[index].name='main().0'


def equivalent_cfg(a,b):
    """Exact labeled-graph bisimulation, hiding only unconditional IR jumps."""
    def resolve(cfg,p):
        seen=set()
        while cfg[p][0]=='goto':
            if p in seen:
                return None
            seen.add(p);p=cfg[p][1]
        return p
    pending=[(a[0],b[0])];seen=set()
    while pending:
        p,q=pending.pop();p=resolve(a[1],p);q=resolve(b[1],q)
        if (p,q) in seen:continue
        seen.add((p,q))
        if p is None or q is None:
            if p!=q:raise ValueError('different unconditional divergence')
            continue
        x,y=a[1][p],b[1][q]
        if x[:2]!=y[:2]:raise ValueError(f'different operations: {x[:2]} != {y[:2]}')
        if x[0] in ('halt','return'):continue
        pending.extend(zip(x[2:],y[2:]))
    return len(seen)


def factor(machine, options):
    """Apply a reproducible alternative to the default factoring pass."""
    from probes import RandomZF2, CostZF2
    probability=options.get('inline_probability')
    seed=options['seed']
    if probability is not None:
        if not 0<=probability<=1:
            raise ValueError('bad inline probability')
        inline_closed(machine,probability,options.get("inline_seed",seed),options.get("inline_main",True))
    machine.grammar_seed=seed
    kind=options['kind']
    if kind=='random':
        RandomZF2.breakout_common_subsequences(machine)
    elif kind=='cost':
        CostZF2.breakout_common_subsequences(machine)
    elif kind=='pair':
        factor_pairs(machine,seed)
    else:
        raise ValueError('unknown grammar kind')


class GrammarCompiler:
    grammar_options=None

    def breakout_common_subsequences(self):
        factor(self,self.grammar_options)


def factor_pairs(machine,seed):
    """Re-Pair-style factoring of the most profitable adjacent pair."""
    from collections import defaultdict
    rng=random.Random(seed)
    while True:
        reach=list(machine.reachable())
        existing={machine.sequences[i].seq for i in reach if len(machine.sequences[i].seq)==2}
        occurrences=defaultdict(list)
        for i in reach:
            seq=machine.sequences[i].seq
            if len(seq)<=2:continue
            for pos in range(len(seq)-1):
                occurrences[seq[pos:pos+2]].append((i,pos))
        choices=[]
        for pair,positions in occurrences.items():
            count=0;previous=None;end=-1
            for i,pos in positions:
                if i!=previous or pos>=end:
                    count+=1;previous=i;end=pos+2
            saving=count-(pair not in existing)
            if saving>0:
                score=saving*(rng.uniform(.6,1.4) if seed else 1)
                choices.append((score,pair))
        if not choices:break
        pair=max(choices,key=lambda x:x[0])[1]
        index=machine.add_sequence(pair)
        for i in reach:
            seq=machine.sequences[i].seq
            if len(seq)<=2:continue
            out=[];pos=0
            while pos<len(seq):
                if seq[pos:pos+2]==pair:
                    out.append(index);pos+=2
                else:
                    out.append(seq[pos]);pos+=1
            machine.sequences[i].seq=tuple(out)
            machine.sequence_lookup[tuple(out)]=i
