"""Explicit instruction trees and checked candidates for dispatcher compression.

The search re-associates binary instruction trees, adjusting relative jumps when
possible, and may commute consecutive increments. None of these search rules
is trusted by the artifact verifier: it checks the complete resulting CFG.
"""
from functools import lru_cache


class Trees:
    def __init__(self, mode="general", commute=True, break_floor=1):
        self.nodes=[];self.lookup={}
        self.mode=mode;self.commute=commute;self.break_floor=break_floor

    def node(self,a,b):
        key=(a,b)
        if key not in self.lookup:
            self.lookup[key]=len(self.nodes);self.nodes.append(key)
        return self.lookup[key]

    def import_machine(self,m):
        @lru_cache(None)
        def visit(v):
            if not isinstance(v,int):return v
            a,b=m.sequences[v].seq
            return self.node(visit(a),visit(b))
        return visit(m.find_seq('main().0'))

    @lru_cache(None)
    def context(self,v):
        if isinstance(v,str):
            if v=='halt':return 0,0
            if v.endswith('.inc'):return 1,0
            if v.endswith('.decnz'):return 2,0
            kind,k=v[1:].split('.');k=int(k)
            return (k+1,0) if kind=='break' else (0,k)
        a,b=self.nodes[v];az,ao=self.context(a);bz,bo=self.context(b)
        return max(az-1,bz,0),max(ao,bo-1,0)

    def closed(self,v):
        z,o=self.context(v)
        return z<=1 and o==0

    def reachable(self,root):
        todo=[root];seen=set()
        while todo:
            v=todo.pop()
            if not isinstance(v,int) or v in seen:continue
            seen.add(v);todo.extend(self.nodes[v])
        return seen

    @lru_cache(None)
    def zeros(self,v):
        return 1+self.zeros(self.nodes[v][0]) if isinstance(v,int) else 0

    def size(self,root):
        """DAG, zero-run dispatcher, and jump states; excludes fixed native states."""
        reach=self.reachable(root)
        jump_break,jump_continue=self.break_floor,4
        for v in reach:
            for bit,child in enumerate(self.nodes[v]):
                if not isinstance(child,str):continue
                if child.startswith('_break.'):
                    jump_break=max(jump_break,int(child.split('.')[1])-(bit==0))
                if child.startswith('_continue.'):
                    jump_continue=max(jump_continue,int(child.split('.')[1])-(bit==1))
        return (len(reach)+max(2,max(self.zeros(v) for v in reach))
                +jump_break+1+jump_continue+1)

    @lru_cache(None)
    def shift_continue(self,v,delta,ones=0):
        """Adjust continues escaping a moved block; reject a lost local target.

        Moving c from ((a,b),c) to (a,(b,c)) adds a right ancestor. An escaping
        continue must cross that extra edge. In the reverse direction, a
        continue targeting the removed (b,c) ancestor cannot be represented.
        """
        if isinstance(v,str):
            if v.startswith('_continue.'):
                k=int(v.split('.')[1])
                if k>ones:
                    if delta<0 and k==ones+1:return None
                    return '_continue.'+str(k+delta)
            return v
        a,b=self.nodes[v]
        x=self.shift_continue(a,delta,ones)
        y=self.shift_continue(b,delta,ones+1)
        if x is None or y is None:return None
        return self.node(x,y)

    @lru_cache(None)
    def shift_break(self,v,delta,zeros=0):
        """Adjust explicit breaks when moving the first block of a rotation.

        Its ordinary return still reaches b. Skipping exactly b may lose its
        representable target; farther explicit breaks can be renumbered.
        A primitive decrement's zero-return distance is fixed, so reject a
        move requiring that instruction itself to change its return distance.
        """
        if isinstance(v,str):
            if v.endswith('.decnz') and zeros==0:return None
            if v.startswith('_break.'):
                k=int(v.split('.')[1])
                if k+1>zeros+1:
                    if delta<0 and k+1==zeros+2:return None
                    return '_break.'+str(k+delta)
            return v
        a,b=self.nodes[v]
        x=self.shift_break(a,delta,zeros+1)
        y=self.shift_break(b,delta,zeros)
        if x is None or y is None:return None
        return self.node(x,y)

    @lru_cache(None)
    def increments_only(self,v):
        if isinstance(v,str):return v.endswith(".inc")
        return all(self.increments_only(x) for x in self.nodes[v])

    def rotations(self,v):
        a,b=self.nodes[v]
        if self.commute and a!=b and self.increments_only(a) and self.increments_only(b):
            yield self.node(b,a)
        if isinstance(a,int):
            x,y=self.nodes[a]
            if self.mode=='basic':
                if self.context(x)[0]<=1 and self.context(b)[1]==0:
                    yield self.node(x,self.node(y,b))
            else:
                shifted=(self.shift_break(x,-1) if self.mode=='general' else
                         x if self.context(x)[0]<=1 else None)
                if shifted is not None:
                    yield self.node(shifted,self.node(y,self.shift_continue(b,1)))
        if isinstance(b,int):
            y,z=self.nodes[b]
            if self.mode=='basic':
                if self.context(a)[0]<=1 and self.context(z)[1]==0:
                    yield self.node(self.node(a,y),z)
            else:
                left=(self.shift_break(a,1) if self.mode=='general' else
                      a if self.context(a)[0]<=1 else None)
                right=self.shift_continue(z,-1)
                if left is not None and right is not None:
                    yield self.node(self.node(left,y),right)

    def replace(self,root,target,replacement):
        @lru_cache(None)
        def visit(v):
            if v==target:return replacement
            if not isinstance(v,int):return v
            a,b=self.nodes[v]
            return self.node(visit(a),visit(b))
        return visit(root)

    def export(self,root):
        nodes=[];known={}
        def visit(v):
            if not isinstance(v,int):return v
            if v not in known:
                a,b=self.nodes[v];pair=[visit(a),visit(b)]
                known[v]=len(nodes);nodes.append(pair)
            return known[v]
        return {'root':visit(root),'nodes':nodes}

    def install(self,m,root):
        from TMBuilder import Sequence
        record=self.export(root)
        m.sequences=[Sequence(tuple(node)) for node in record['nodes']]
        m.sequence_lookup={seq.seq:i for i,seq in enumerate(m.sequences)}
        m.sequences[record['root']].name='main().0'
        m.memo={}

    def compact(self, roots):
        fresh=Trees(self.mode,self.commute,self.break_floor)
        @lru_cache(None)
        def visit(v):
            if not isinstance(v,int):return v
            a,b=self.nodes[v]
            return fresh.node(visit(a),visit(b))
        return fresh,[visit(v) for v in roots]

    def clear_caches(self):
        # Method caches otherwise keep discarded interning arenas alive.
        for method in (self.context, self.zeros, self.shift_continue,
                       self.shift_break, self.increments_only):
            method.cache_clear()

    def import_record(self, record, registers=None):
        """Validate a finite, topologically ordered tree before interning it."""
        import re
        if not isinstance(record, dict) or set(record) != {'root', 'nodes'}:
            raise ValueError('instruction tree requires root and nodes')
        nodes=record['nodes'];root=record['root']
        if not isinstance(nodes,list) or type(root) is not int or not 0<=root<len(nodes):
            raise ValueError('invalid instruction-tree root')
        mapping={}
        for i,pair in enumerate(nodes):
            if not isinstance(pair,list) or len(pair)!=2:
                raise ValueError('instruction-tree node must have two children')
            out=[]
            for child in pair:
                if type(child) is int:
                    if not 0<=child<i:raise ValueError('forward or cyclic instruction-tree reference')
                    out.append(mapping[child])
                elif isinstance(child,str):
                    op=re.fullmatch(r'3\.([A-Za-z0-9_]+)\.(inc|decnz)',child)
                    jump=re.fullmatch(r'_(break|continue)\.[0-9]+',child)
                    if not (op or jump or child=='halt'):
                        raise ValueError('unknown instruction-tree primitive')
                    if op and registers is not None and op[1] not in registers:
                        raise ValueError('unknown instruction-tree register')
                    out.append(child)
                else:raise ValueError('invalid instruction-tree child')
            mapping[i]=self.node(*out)
        return mapping[root]


def read_record(record, directory):
    """Load and hash-check the small tree artifact named by a configuration."""
    import hashlib
    import json
    from pathlib import Path
    filename=record.get('instruction_tree')
    if filename is None:return None
    data=(Path(directory)/filename).read_bytes()
    if hashlib.sha256(data).hexdigest()!=record.get('instruction_tree_sha256'):
        raise ValueError('instruction-tree artifact hash mismatch')
    return json.loads(data)


class TreeCompiler:
    """Install an explicit final IR tree; native register kernels are unchanged."""
    def reduce_to_cons(self):
        super().reduce_to_cons()
        tree=Trees()
        root=tree.import_record(self.instruction_tree_record,self.registers)
        tree.install(self,root)
        tree.clear_caches()
