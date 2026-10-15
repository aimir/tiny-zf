"""Explicit compiler and checked local transformations for Mira's native backend.

The compiler keeps the pinned register kernel and emits a separate decoder for
an instruction tree. Symbolic checking is a screen; acceptance requires the
Coq candidate checker. Numeric names deliberately retain the kernel addresses.
"""
from pathlib import Path
import argparse
import hashlib
import json
from compare_mira254 import checked_inputs, normalized_table, recover, symbolic_check

KERNEL = frozenset(map(str, [0,1,2,3,4,5,6,7,8,9,10,13,14,19,20,28,29,30,31,38,40,41,
    42,43,44,48,56,57,58,59,60,63,64,69,73,74,75,83,84,85,95,97,109,112,131]))
SKIP = dict(wffstack='60', param1='44', axiomcode='31', scratch2='56', scratch1='38',
            prooflist='40', nextproof='28', topwff='64', param2='69')
MERGES = [
    ('360','487','0',('0','L','366')),
    ('304','c2','0',('0','R','3.nextproof.inc')),
    ('379','391','0',('0','L','376')),
    ('341','472','1',('1','L','347')),
    ('302','316','1',('1','L','472')),
    ('426','441','1',('1','L','425')),
]


def prune(table, start='0'):
    todo=[start]; seen=set()
    while todo:
        q=todo.pop()
        if q in seen or q=='halt': continue
        seen.add(q)
        todo.extend(table[q,b][2] for b in ('0','1'))
    return {k:v for k,v in table.items() if k[0] in seen}


def write_table(path, table):
    path=Path(path); path.parent.mkdir(parents=True,exist_ok=True)
    path.write_text('#! start 0\n'+'\n'.join(' '.join((q,b,w,d,'254' if t=='halt' else t))
        for (q,b),(w,d,t) in sorted(table.items()))+'\n')


def compile_native(directory, tree, root, boot_root=193):
    _, original=normalized_table(directory)
    table={k:v for k,v in original.items() if k[0] in KERNEL}
    def control(kind,k):
        if k<0: raise ValueError('negative control depth')
        if k==0: return '7' if kind=='break' else '2'
        name=('b' if kind=='break' else 'c')+str(k)
        prev=control(kind,k-1)
        if kind=='break':
            table[name,'0']=('0','L',prev); table[name,'1']=('0','L',name)
        else:
            table[name,'0']=('0','L',name); table[name,'1']=('0','L',prev)
        return name
    def edge(child,bit):
        if isinstance(child,int): return (bit,'R',str(300+child))
        if child=='halt': return (bit,'R','halt')
        if child.startswith('_'):
            kind,k=child[1:].split('.'); k=int(k)
            if kind=='continue': return ('0','L',control(kind,k-int(bit)))
            if bit=='0':
                return ('1','L','2') if k==0 else ('0','L',control(kind,k-1))
            return ('0','L',control(kind,k))
        _,reg,op=child.split('.')
        table[child,'0']=('0','R','57' if op=='inc' else '30')
        table[child,'1']=('0','R',SKIP[reg])
        return (bit,'R',child)
    for v in sorted(tree.reachable(root) | tree.reachable(boot_root) | tree.reachable(6)):
        for bit,child in enumerate(tree.nodes[v]): table[str(300+v),str(bit)]=edge(child,str(bit))
    table['96','0']=table[str(300+root),'0']; table['96','1']=table[str(300+root),'1']
    table={k:(w,d,'96' if t==str(300+root) else t) for k,(w,d,t) in table.items()}
    table['8','0']=tuple(str(300+boot_root) if x=='11' else x for x in table['8','0'])
    table['8','1']=tuple('306' if x=='12' else x for x in table['8','1'])
    return prune(table)


def merge(table, removed, survivor, bit, edge):
    if removed==survivor or any(q in KERNEL or q=='96' for q in (removed,survivor)):
        raise ValueError('cannot alter a protected kernel state')
    if (removed,'0') not in table or (survivor,'0') not in table: raise ValueError('missing merge state')
    table={k:(w,d,survivor if t==removed else t) for k,(w,d,t) in table.items() if k[0]!=removed}
    table[survivor,bit]=tuple(edge)
    return prune(table)


def contextual_rotation(directory):
    """Reassociate node 74 while preserving its use by a backtracking decoder.

    State 218 reaches 154 on a leftward excursion. Its zero case still needs
    the old node-74 zero edge. State 206 supplies that edge, so a separate
    copy of 154 repairs this context while ordinary dispatch uses the rotation.
    This trades removed state 208 for g154, retaining 254 states.
    """
    _, table = normalized_table(directory)
    table['178', '0'] = ('0', 'R', '16')
    table['178', '1'] = ('1', 'R', '206')
    table['g154', '0'] = ('0', 'R', '206')
    table['g154', '1'] = table['154', '1']
    table['218', '0'] = ('0', 'L', 'g154')
    return prune(table)


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--upstream',type=Path,required=True);p.add_argument('--output',type=Path,required=True)
    p.add_argument('--backend', choices=('independent', 'contextual'), default='independent')
    p.add_argument('--merges',type=int,choices=range(7));p.add_argument('--rotate',action='store_true')
    a=p.parse_args();directory=checked_inputs(a.upstream)
    tree,root,_=recover((directory/'coq/tm/Prog254.v').read_text(),True)
    boot=193
    if a.rotate:
        replacement=tree.node(48,63);root=tree.replace(root,74,replacement);boot=tree.replace(193,74,replacement)
    if a.backend == 'contextual':
        if not a.rotate or a.merges not in (None, 0):
            p.error('contextual backend requires --rotate and no independent merges')
        a.merges=0
        table=contextual_rotation(directory)
    else:
        if a.merges is None: a.merges=6
        table=compile_native(directory,tree,root,boot)
        for step in MERGES[:a.merges]: table=merge(table,*step)
    write_table(a.output,table)
    tree_path=a.output.with_suffix('.tree.json')
    tree_path.write_text(json.dumps(tree.export(root),indent=2)+'\n')
    result=symbolic_check(directory,a.output,tree,root)
    report=dict(states=len(table)//2,backend=a.backend,merges=a.merges,rotation=a.rotate,
                machine_sha256=hashlib.sha256(a.output.read_bytes()).hexdigest(),
                tree_sha256=hashlib.sha256(tree_path.read_bytes()).hexdigest(),symbolic=result)
    a.output.with_suffix('.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report),flush=True)
    if not result['passed']: raise SystemExit(1)

if __name__=='__main__': main()
