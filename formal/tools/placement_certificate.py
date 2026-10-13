"""Propose exact placements of the proved structured source in its finite graph.

This matcher is untrusted. Its output must be accepted by Graph.Models using
literal instruction and jump checks; it supplies no semantic assumptions.
"""
from pathlib import Path


def seq(*codes):
    out = ('skip',)
    for code in reversed(codes):
        out = ('seq', code, out)
    return out


def two(a, b): return ('seq', a, b)
def inc(r): return ('inc', r)
def move(r, ds): return ('while', r, seq(*(inc(d) for d in ds)))
def clear(r): return move(r, [])
def copy_keep(r,t,d): return two(move(r,[t,d]),move(t,[r]))
def unpair(i,a,b): return ('while',i,two(inc(a),('if',b,('skip',),move(a,[b]))))
def pair(o,a,b): return two(move(a,[b,o]),('while',b,two(inc(o),two(move(b,[a]),move(a,[b,o])))))
def equal(a,b,body):
    loop=('while',a,('if',b,('skip',),two(clear(a),('break',1))))
    return ('block',two(loop,('if',b,two(clear(b),('break',0)),body)))
def push(): return two(move(3,[8]),two(pair(9,2,8),move(9,[3])))
def param(r): return two(push(),two(move(r,[8,2]),move(8,[r])))
def cons(): return two(unpair(3,8,9),two(move(9,[3]),two(pair(9,2,8),move(9,[2]))))
def tag(k): return two(seq(*(inc(8) for _ in range(k))),two(pair(9,2,8),move(9,[2])))
def binary(k): return two(cons(),tag(k))
def select(): return two(unpair(3,8,9),two(move(9,[3]),two(('if',4,('skip',),two(clear(2),move(8,[2]))),clear(8))))
def take(r):
    return ('if',4,('if',4,two(inc(4),inc(4)),two(inc(4),two(unpair(3,8,9),two(move(9,[3]),two(clear(r),move(8,[r])))))),('skip',))
def safety(a,b): return two(copy_keep(a,8,9),two(copy_keep(b,8,2),equal(9,2,inc(a))))
def protect(): return two(push(),two(safety(5,6),two(safety(7,6),two(unpair(3,8,9),two(move(9,[3]),move(8,[2]))))))
def expr(tree):
    if tree[0]=='param': return param(5+tree[1])
    if tree[0]=='unary': return two(expr(tree[2]),tag(tree[1]))
    return two(expr(tree[2]),two(expr(tree[3]),binary(tree[1])))
def expression(rpn, permutation):
    stack=[]
    for token in rpn.split():
        if token.startswith('p'): stack.append(('param',permutation[int(token[1:])-1]-1))
        elif token=='wn': stack.append(('unary',3,stack.pop()))
        else:
            b,a=stack.pop(),stack.pop()
            if token=='wex': out=('unary',3,('binary',4,a,('unary',3,b)))
            elif token=='wa': out=('unary',3,('binary',2,a,('unary',3,b)))
            else: out=('binary',{'weq':0,'wel':1,'wim':2,'wal':4}[token],a,b)
            stack.append(out)
    assert len(stack)==1
    return stack[0]
def generalize(): return two(take(7),two(expr(('binary',4,('param',0),('param',2))),select()))
def detach():
    compare=two(move(2,[9]),two(copy_keep(6,8,2),equal(9,2,copy_keep(5,8,2))))
    return two(take(7),two(take(6),two(expr(('binary',2,('param',2),('param',0))),two(compare,select()))))
def halt_check(): return ('if',2,('if',2,two(inc(2),inc(2)),('halt',)),('skip',))
def enumeration(): return ('if',0,('skip',),two(move(1,[8,0]),two(move(8,[1]),inc(1))))


def source_phases(record):
    from ics import RPN,LOGICAL,PROTECTED
    from joint import LOGIC_RPN,PERMUTATIONS
    from formula_rewrite import rewrite
    from decoder import allocation_plan
    from graph_certificate import REGISTERS
    decoder=[]
    for op in allocation_plan(record['decoder']):
        if op[0]=='clear': decoder.append(clear(REGISTERS.index(op[1])))
        elif op[0]=='move': decoder.append(move(REGISTERS.index(op[1]),[REGISTERS.index(op[2])]))
        else: decoder.append(unpair(REGISTERS.index(op[3]),REGISTERS.index(op[1]),REGISTERS.index(op[2])))
    result=[('enumeration','Decoding.enumerationPrefix',enumeration()),
            ('decoder','Decoding.lowerList TinyZF.Decoder.plan',seq(*decoder)),
            ('push','FormulaStack.push',push())]
    names=list(LOGICAL[2:])+list(PROTECTED)
    for j,clause in enumerate(record['order']):
        if j==12: result.append(('protect','Clauses.protect',protect()))
        if clause==0: result.append(('detach','Clauses.detach',detach()))
        elif clause==1: result.append(('generalize','Clauses.generalize',generalize()))
        else:
            k=clause-2; name=names[k];protected=name in PROTECTED
            perm=PERMUTATIONS[record['protected_permutation'] if protected else record['parameter_permutations'][name]]
            rpn=rewrite(RPN[name],record['formula_choices'][name]) if protected else LOGIC_RPN[name]
            result.append((name,f'Clauses.expressionClause (SchemaCode.expression {k})',two(expr(expression(rpn,perm)),select())))
    result.append(('halt','Execution.haltCheck',halt_check()))
    return result


class Matcher:
    def __init__(self,graph): self.graph=graph
    def chase(self,q):
        edges=[]
        while self.graph[q][0]=='jump':
            q=self.graph[q][1]
            if q in edges: raise ValueError('control-only cycle')
            edges.append(q)
        return q,edges
    def infer(self,c,q):
        """Record the actual control flow for every structured constructor."""
        kind=c[0]
        actual,before=self.chase(q)
        op=self.graph[actual]
        children=[]; extra={}; exits={}
        def merge(es):
            for k,v in es.items():
                if k in exits and exits[k]!=v: raise ValueError(f'conflicting exits {kind}@{q}: {k} {exits[k]} vs {v}')
                exits[k]=v
        if kind=='skip': exits['normal']=actual
        elif kind=='inc':
            assert op[:2]==('inc',c[1]),(kind,q,c,op)
            nxt,after=self.chase(op[2]);exits['normal']=nxt;extra['after']=after
        elif kind=='break': exits[c[1]]=actual
        elif kind=='halt':
            assert op[0]=='halt',(kind,q,op)
            exits['halt']=None
        elif kind=='seq':
            left=self.infer(c[1],q);children.append(left)
            if 'normal' not in left['exits']:
                raise ValueError(f'unreachable sequence tail at {q}: {c[2][0]}')
            right=self.infer(c[2],left['exits']['normal']);children.append(right)
            merge({k:v for k,v in left['exits'].items() if k!='normal'});merge(right['exits'])
        elif kind=='if':
            assert op[:2]==('decnz',c[1]),(kind,q,c[1],op)
            for child,entry in zip(c[2:],op[2:]):
                node=self.infer(child,entry);children.append(node);merge(node['exits'])
        elif kind=='while':
            assert op[:2]==('decnz',c[1]),(kind,q,c[1],op)
            nxt,after=self.chase(op[3]);extra['after']=after
            node=self.infer(c[2],op[2]);children.append(node)
            if 'normal' in node['exits']: assert node['exits']['normal']==actual,('loop return',q,node['exits']['normal'],actual)
            if 0 in node['exits']: assert node['exits'][0]==nxt,('loop break',q,node['exits'][0],nxt)
            exits['normal']=nxt
            merge({(k-1 if isinstance(k,int) else k):v for k,v in node['exits'].items() if k not in ('normal',0)})
        elif kind=='block':
            node=self.infer(c[1],q);children.append(node)
            for k,v in node['exits'].items():
                merge({('normal' if k==0 else k-1 if isinstance(k,int) else k):v})
        else: raise ValueError(kind)
        return dict(code=c,q=q,actual=actual,before=before,exits=exits,children=children,op=op,**extra)


def placement_source(root, record):
    from joint import build_joint,decode
    from graph_certificate import extract
    m=build_joint(decode(record),sharing=record['shared_operations'],formula_choices=record['formula_choices'],compile_machine=False,decoder=record['decoder'])
    start,graph=extract(m,m.main());matcher=Matcher(graph);q=start;nodes=[]
    for name,lean,code in source_phases(record):
        node=matcher.infer(code,q);q=node['exits']['normal'];nodes.append((name,lean,node))
    assert q==start
    def jumps(q, successors, stop):
        if not successors:
            assert q==stop
            return '(Jumps.done _)'
        return '(checkJumps_sound _ '+str(q)+' ['+', '.join(map(str,successors))+'] '+str(stop)+' (by decide +kernel))'
    def proof(node,next,indent=2):
        kind=node['code'][0];pad=' '*indent;q=node['q'];actual=node['actual'];op=node['op'];kids=node['children']
        before=jumps(q,node['before'],actual)
        if kind=='skip': return [pad+f'exact Models.skip {before}']
        if kind=='inc': return [pad+f'exact Models.inc {before} (by decide +kernel) {jumps(op[2],node["after"],next)}']
        if kind=='halt': return [pad+f'exact Models.halt {before} (by decide +kernel)']
        if kind=='break': return [pad+f'exact Models.breakLoop {before}']
        if kind=='seq':
            mid=kids[0]['exits']['normal']
            return [pad+f'apply Models.seq (mid := {mid})',pad+'·']+proof(kids[0],mid,indent+2)+[pad+'·']+proof(kids[1],next,indent+2)
        if kind=='if':
            return [pad+f'apply Models.ifDec (actual := {actual}) (yes := {op[2]}) (no := {op[3]}) {before} (by decide +kernel)',pad+'·']+proof(kids[0],next,indent+2)+[pad+'·']+proof(kids[1],next,indent+2)
        if kind=='while':
            return [pad+f'apply Models.whileDec (actual := {actual}) (bodyEntry := {op[2]}) (zero := {op[3]}) {before} (by decide +kernel) {jumps(op[3],node["after"],next)}']+proof(kids[0],actual,indent)
        if kind=='block': return [pad+'apply Models.block']+proof(kids[0],next,indent)
        raise ValueError(kind)
    lines=['import TinyZF.Interpreter.Execution','import TinyZF.Interpreter.SourceGraph','',
        'set_option maxHeartbeats 0','set_option maxRecDepth 16384','set_option Elab.async false','',
        '/-! # Exact placement of the structured source in its primitive graph','',
        'Generated witnesses are checked against every actual register instruction,',
        'branch, loop back-edge, and control-only jump. Each private lemma covers one',
        'meaningful interpreter phase; `models` composes them into the whole iteration.',
        'The Python matcher and source compiler are not trusted. -/',
        'namespace TinyZF.Interpreter.Placement','open Graph','']
    for name,lean,node in nodes:
        next=node['exits']['normal']
        lines += [f'/-- Literal placement of the {name} phase, from entry {node["q"]} to normal return {next}. -/',
                  f'private theorem place_{name} (breaks : Nat → Fin 6741) :',
                  f'    Models SourceGraph.program breaks ({lean}) {node["q"]} {next} := by']
        lines += proof(node,next)+['']
    lines += ['/-- The entire source iteration occupies exactly the unoptimized graph.',
              ' Normal returns go to its actual start; the only halt is the final target test. -/',
              'theorem models : Models SourceGraph.program (fun _ => 0)',
              '    Execution.code SourceGraph.start SourceGraph.start := by',
              '  apply Models.seq (place_enumeration _)',
              '  apply Models.seq (place_decoder _)',
              '  apply Models.seq (place_push _)',
              '  apply Models.seq (mid := 6735)', '  ·']
    for name,_,_ in nodes[3:-1]: lines += [f'    apply Models.seq (place_{name} _)']
    lines += ['    exact Models.skip (Jumps.done _)','  · exact place_halt _','',
              'end TinyZF.Interpreter.Placement','']
    return '\n'.join(lines)
