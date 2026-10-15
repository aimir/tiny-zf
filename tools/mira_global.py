"""Checkpointed semantic transition search for the pinned Mira interpreter.

The symbolic checks are search filters, not formal verification. Accepted
tables must subsequently pass the complete Coq proof with their literal rows.
"""
import argparse
from collections import defaultdict
import hashlib
import itertools
import json
from pathlib import Path
import time

from compare_mira254 import checked_inputs, recover, paths, normalized_table
from instruction_tree import Trees

KERNEL = frozenset(map(str, [0,1,2,3,4,5,6,7,8,9,10,13,14,19,20,28,29,30,31,38,40,41,
    42,43,44,48,56,57,58,59,60,63,64,69,73,74,75,83,84,85,95,97,
    109,112,131,96]))
BOX_KERNEL = frozenset(map(str,[0,1,2,3,4,6,28,31,38,40,43,44,48,56,
    59,60,63,64,69,73,75,83,85,95,97,109,112,131,96]))
SKIP = {'69':7,'64':6,'28':5,'40':4,'38':3,'56':2,'31':1,'44':0,'60':-1}
REG = dict(wffstack=0,param1=1,axiomcode=2,scratch2=3,scratch1=4,
           prooflist=5,nextproof=6,topwff=7,param2=8)


class Recording(dict):
    def __getitem__(self, key):
        self.observed.add(key)
        return super().__getitem__(key)


class Oracle:
    def __init__(self, upstream, tree=None, root=None, table=None, verify=True, d0=40):
        self.d0=d0
        self.protected=KERNEL
        self.mutable_anchor_rows=frozenset()
        self.directory = checked_inputs(Path(upstream))
        self.tree, self.root, _ = recover((self.directory/'coq/tm/Prog254.v').read_text(), True)
        if tree is not None:
            self.tree, self.root = tree, root
        _, edges = normalized_table(self.directory)
        self.table = {(q,int(b)):(int(w),d,'254' if t=='halt' else t)
                      for (q,b),(w,d,t) in edges.items()}
        if table is not None:
            self.table = table
        source = (self.directory/'tools/tm/symexec.py').read_text()
        source = source[source.index('class Fail'):source.index('paths = json.load')]
        source = source.replace('fuel=20000','fuel=2000')
        self.ns = dict(D0=d0,SKIP=SKIP,REG=REG)
        exec(compile(source,'pinned-symexec.py','exec'), self.ns)
        canon, inc, strip, tape = (self.ns[n] for n in ('canon','inc','strip','tape_R'))
        self.cases = []
        self.by_edge = defaultdict(list)
        self.trials = 0
        for p,op in paths(self.tree,self.root):
            Q=p[3:]
            variants = [('z','dec0'),('p','dec')] if op.endswith('.decnz') else [('-', 'inc' if op.endswith('.inc') else None)]
            for branch,effect in variants:
                if op.endswith('.inc') or (op.endswith('.decnz') and branch=='p'): Q2=inc(Q)
                elif op.endswith('.decnz'): Q2=inc(strip('0',1,Q))
                elif op.startswith('_continue'): Q2=strip('1',int(op.split('.')[1]),Q)
                elif op.startswith('_break'): Q2=inc(strip('0',int(op.split('.')[1]),Q))
                else: Q2=''
                e=() if effect is None else ((effect,REG[op.split('.')[1]]),)
                expect=canon([('b',1)], [('r',0,1,d0+1),('b',1),('box',('plain',)+e)]) if Q2 is None else canon([('b',1)],tape(Q2,0,e))
                self.cases.append((tape(Q,0,()),branch,expect,'halt' if op=='halt' else 'ok'))
        if verify:
            self.rebase(self.table)
        else:
            self.ns['T']=self.table

    def rebase(self, table):
        self.table = table
        self.by_edge = defaultdict(list)
        recording=Recording(self.table)
        recording.observed=set()
        self.ns['T']=recording
        largest=0
        for i in range(len(self.cases)):
            recording.observed.clear()
            out=self.run_case(i)
            if not out: raise ValueError(f'baseline failed case {i}')
            largest=max(largest,out[1])
            for edge in recording.observed: self.by_edge[edge].append(i)
        self.ns['T']=self.table
        print(f'baseline {len(self.cases)} cases; max symbolic steps {largest}',flush=True)

    def run_case(self,i):
        tape,branch,expect,want=self.cases[i]
        try: out=self.ns['run']('96',[('b',1)],tape,branch,expect)
        except (self.ns['Fail'],KeyError): return False
        return out if out[0]==want else False

    def check_edge(self,key,edge):
        original=self.table[key]
        self.table[key]=edge
        self.trials+=1
        affected=self.by_edge[key]
        try:
            for j,i in enumerate(affected):
                if not self.run_case(i):
                    if j: affected.insert(0,affected.pop(j))
                    return False
            return True
        finally: self.table[key]=original

    def check(self,table):
        self.ns['T']=table
        try:
            for i in range(len(self.cases)):
                if not self.run_case(i): return False,i
            return True,None
        finally: self.ns['T']=self.table


def bootstrap(table,limit=2000000):
    """Exact finite bootstrap comparison, including all trailing registers."""
    expected={-1,62,77,78}|{64+2*i+(2 if i>6 else 0) for i in range(145)}
    tape=set(); q='0'; head=0
    for step in range(limit+1):
        if q=='96' and {p-head for p in tape}==expected: return step
        if step==limit: break
        edge=table.get((q,int(head in tape)))
        if edge is None: return None
        w,d,q=edge
        if w: tape.add(head)
        else: tape.discard(head)
        head+=1 if d=='R' else -1
    return None


def save_json(path,data):
    temp=path.with_suffix('.tmp')
    temp.write_text(json.dumps(data,indent=2)+'\n')
    temp.replace(path)


def load_options(path):
    return json.loads(path.read_text()) if path.exists() else {}


def state_key(q):
    return (0,int(q)) if q.isdigit() else (1,q)


def checkpoint_identity(oracle,folder):
    identity=dict(
        table_sha256=hashlib.sha256(repr(sorted(oracle.table.items())).encode()).hexdigest(),
        cases_sha256=hashlib.sha256(repr(oracle.cases).encode()).hexdigest(),
        protected_states=sorted(oracle.protected,key=state_key),
        mutable_anchor_rows=[list(row) for row in sorted(oracle.mutable_anchor_rows)],
        minimum_gap=oracle.d0,
        symbolic_fuel=2000)
    path=folder/'identity.json'
    if path.exists():
        previous=json.loads(path.read_text())
        previous.setdefault('mutable_anchor_rows',[])
        previous.setdefault('minimum_gap',40)
        if previous!=identity:
            raise ValueError('checkpoint belongs to a different table/program/kernel/fuel')
    save_json(path,identity)


def learn(oracle,folder,mode):
    checkpoint_identity(oracle,folder)
    target=folder/'options.json'
    options=load_options(target)
    states=sorted({q for q,b in oracle.table},key=state_key)
    edges=[(w,d,q) for w in (0,1) for d in ('L','R') for q in states+['254']]
    began=time.monotonic()
    def one(q,b):
        key=f'{q}:{b}'
        if key in options: return
        if q in oracle.protected and (q,b) not in oracle.mutable_anchor_rows:
            options[key]=[oracle.table[q,b]]
        else:
            allowed=[e for e in edges if e==oracle.table[q,b] or oracle.check_edge((q,b),e)]
            options[key]=allowed
        save_json(target,options)
        print(f'learn {key} {len(options[key])} alternatives, {len(oracle.by_edge[q,b])} cases, {oracle.trials} trials, {time.monotonic()-began:.1f}s',flush=True)
    for q in states: one(q,0)
    if mode=='all':
        for q in states: one(q,1)
    else:
        # Learn second reads only for plausible pairs not already exhausted by
        # retaining a common original row and replacing the other row.
        candidates=[]
        for i,q in enumerate(states):
            if q in oracle.protected: continue
            eq=set(map(tuple,options[f'{q}:0']))
            for s in states[:i]:
                if s in oracle.protected: continue
                common=eq&set(map(tuple,options[f'{s}:0']))
                if common and not (common=={oracle.table[q,0]} and oracle.table[q,0]==oracle.table[s,0]):
                    candidates.append((len(oracle.by_edge[q,1])+len(oracle.by_edge[s,1]),q,s))
        for _,q,s in sorted(candidates):
            one(q,1); one(s,1)
            common0=set(map(tuple,options[f'{q}:0']))&set(map(tuple,options[f'{s}:0']))
            common1=set(map(tuple,options[f'{q}:1']))&set(map(tuple,options[f'{s}:1']))
            if common1:
                print(f'pair {q} {s}: {len(common0)} x {len(common1)} common edges',flush=True)
                for e0,e1 in itertools.product(common0,common1):
                    candidate={key:(w,d,s if t==q else t) for key,(w,d,t) in oracle.table.items() if key[0]!=q}
                    candidate[s,0]=(e0[0],e0[1],s if e0[2]==q else e0[2])
                    candidate[s,1]=(e1[0],e1[1],s if e1[2]==q else e1[2])
                    valid,case=oracle.check(candidate)
                    if valid and (steps:=bootstrap(candidate)) is not None:
                        if hasattr(oracle,'confirm') and not oracle.confirm(candidate)[0]:
                            raise ValueError('native/Python disagreement on a candidate')
                        result=folder/f'candidate-merge-{q}-{s}.tm'
                        write_table(result,candidate)
                        save_json(result.with_suffix('.json'),dict(removed=q,survivor=s,edges=[e0,e1],bootstrap_steps=steps))
                        print(f'FOUND {result}',flush=True)


def write_table(path,table):
    rows=['#! start 0']+[' '.join(map(str,(q,b,w,d,t))) for (q,b),(w,d,t) in sorted(table.items(),key=lambda item:(state_key(item[0][0]),item[0][1]))]
    path.write_text('\n'.join(rows)+'\n')


def solve(oracle,folder,target,seconds,options_file=None):
    """Find a global quotient choosing among individually checked row rewrites.

    Alternative rewrites need not compose. The extracted whole table is
    therefore checked again; SAT only proposes candidates.
    """
    import z3
    checkpoint_identity(oracle,folder)
    raw=load_options(options_file or folder/'options.json')
    names=sorted({q for q,b in oracle.table},key=state_key)
    n=len(names)
    names.append('254')
    indices={q:i for i,q in enumerate(names)}
    options={(q,b):[tuple(e) for e in raw.get(f'{names[q]}:{b}',[oracle.table[names[q],b]])]
             for q in range(n) for b in (0,1)}
    for q in range(n):
        if names[q] in oracle.protected:
            for b in (0,1):
                if (names[q],b) not in oracle.mutable_anchor_rows:
                    options[q,b]=[oracle.table[names[q],b]]
    # Kernel identities are anchors. Other states may be absorbed by an anchor
    # while its literal row survives; two distinct anchors cannot be identified.
    possible={(q,s) for q in range(n+1) for s in range(n+1)
              if q==s or q<n and s<n and not (names[q] in oracle.protected and names[s] in oracle.protected)}
    def supported(q,s,b):
        return any(w==w2 and d==d2 and (indices[t],indices[t2]) in possible
                   for w,d,t in options[q,b] for w2,d2,t2 in options[s,b])
    rounds=0
    while True:
        remove={(q,s) for q,s in possible if q!=s and
                (not supported(q,s,0) or not supported(q,s,1))}
        if not remove: break
        possible-=remove; rounds+=1
    pairs=sorted((q,s) for q,s in possible if q>s)
    print(f'greatest compatible relation: {len(pairs)} pairs after {rounds} rounds',flush=True)
    save_json(folder/'compatibility.json',dict(learned_rows=len(raw),pairs=[(names[q],names[s]) for q,s in pairs],rounds=rounds))
    if not pairs: return
    S=z3.Solver(); S.set(timeout=1000*seconds)
    C=[z3.Int(f'c_{q}') for q in range(n)]+[z3.IntVal(n)]
    for q in range(n):
        values=[q] if names[q] in oracle.protected else [s for s in range(n) if (s<=q or names[s] in oracle.protected) and (q,s) in possible]
        S.add(z3.Or([C[q]==s for s in values]))
        for s in values:
            if s!=q: S.add(z3.Implies(C[q]==s,C[s]==s))
    S.add(z3.Sum([z3.If(C[q]==q,1,0) for q in range(n)])<=target)
    selectors={}
    for b in (0,1):
        W=z3.Array(f'w{b}',z3.IntSort(),z3.IntSort())
        D=z3.Array(f'd{b}',z3.IntSort(),z3.IntSort())
        T=z3.Array(f't{b}',z3.IntSort(),z3.IntSort())
        for q in range(n):
            rows=options[q,b]
            K=z3.Int(f'k{q}_{b}'); selectors[q,b]=K
            S.add(z3.Or([z3.And(K==i,W[C[q]]==w,D[C[q]]==(1 if d=='R' else -1),T[C[q]]==C[indices[t]])
                         for i,(w,d,t) in enumerate(rows)]))
    for attempt in range(32):
        result=S.check()
        print(f'solver attempt {attempt}: {result}',flush=True)
        if result!=z3.sat: break
        model=S.model()
        classes=[model.eval(c).as_long() for c in C]
        selected={key:model.eval(k).as_long() for key,k in selectors.items()}
        candidate={}
        for q in range(n):
            for b in (0,1):
                w,d,t=options[q,b][selected[q,b]]
                key=names[classes[q]],b
                value=w,d,names[classes[indices[t]]]
                if key in candidate and candidate[key]!=value:
                    raise AssertionError('inconsistent quotient extraction')
                candidate[key]=value
        valid,case=oracle.check(candidate)
        steps=bootstrap(candidate) if valid else None
        print(f'candidate {len(candidate)//2} states: symbolic={valid} case={case} bootstrap={steps}',flush=True)
        if valid and steps is not None:
            if hasattr(oracle,'confirm') and not oracle.confirm(candidate)[0]:
                raise ValueError('native/Python disagreement on a candidate')
            path=folder/f'global-{len(candidate)//2}-{attempt}.tm'
            write_table(path,candidate)
            save_json(path.with_suffix('.json'),dict(classes={names[q]:names[classes[q]] for q in range(n)},selected={f'{names[q]}:{b}':i for (q,b),i in selected.items()},bootstrap_steps=steps))
            print(f'FOUND {path}',flush=True)
        # Block precisely this set of row choices and representatives.
        S.add(z3.Or([C[q]!=classes[q] for q in range(n)]+
                    [k!=selected[key] for key,k in selectors.items() if len(options[key])>1]))


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--upstream',type=Path,required=True)
    parser.add_argument('--output',type=Path,required=True)
    parser.add_argument('--learn',choices=['focused','all'],default='focused')
    parser.add_argument('--solve',action='store_true')
    parser.add_argument('--target',type=int,default=253)
    parser.add_argument('--seconds',type=int,default=120)
    parser.add_argument('--rotated',action='store_true')
    parser.add_argument('--table',type=Path)
    parser.add_argument('--tree',type=Path)
    parser.add_argument('--relax-dispatch',action='store_true')
    parser.add_argument('--options',type=Path)
    parser.add_argument('--relax-anchor-rows',action='store_true')
    parser.add_argument('--native',type=Path,help='optional compiled search filter library')
    parser.add_argument('--d0',type=int,default=40,help='symbolic minimum dispatcher gap')
    args=parser.parse_args()
    args.output.mkdir(parents=True,exist_ok=True)
    tree=root=table=None
    if args.rotated:
        directory=checked_inputs(args.upstream)
        tree,root,_=recover((directory/'coq/tm/Prog254.v').read_text(),True)
        root=tree.replace(root,74,tree.node(48,63))
    if args.tree:
        data=json.loads(args.tree.read_text());tree=Trees()
        for i,pair in enumerate(data['nodes']):
            if len(pair)!=2 or any(isinstance(v,int) and not 0<=v<i for v in pair):
                raise ValueError('tree must be a postorder binary DAG')
            if tree.node(*pair)!=i: raise ValueError('tree has duplicate nodes')
        root=data['root']
        if not isinstance(root,int) or not 0<=root<len(tree.nodes):
            raise ValueError('invalid tree root')
    if args.table:
        table={}
        for line in args.table.read_text().splitlines():
            if not line or line.startswith('#'): continue
            q,b,w,d,t=line.split()
            table[q,int(b)]=int(w),d,t
    oracle=Oracle(args.upstream,tree,root,table,d0=args.d0)
    if args.relax_dispatch: oracle.protected=BOX_KERNEL
    if args.relax_anchor_rows:
        oracle.mutable_anchor_rows=frozenset([('3',0),('6',0),('48',0),('69',1)])
    if args.native:
        from mira_global_native import NativeOracle
        oracle=NativeOracle(oracle,args.native)
    if args.solve: solve(oracle,args.output,args.target,args.seconds,args.options)
    else: learn(oracle,args.output,args.learn)


if __name__=='__main__': main()
