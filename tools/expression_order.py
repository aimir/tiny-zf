"""Evaluate formula subtrees in different orders with consistent payload coding.

The arithmetic constructor still pairs the top operand with the popped operand.
Reversing evaluation for one operator therefore reverses that operator's formula
payload convention. Tags stay fixed and the two distinguished zero-argument
formulas keep codes zero and one. DET/GEN use the same operator conventions.
"""

BINARY=('weq','wel','wim','wal')

class ExpressionOrder:
    expression_mask=0

    def constructor_sequence(self,source,permutation):
        stack=[]
        for t in source.split():
            if t.startswith('p'):stack.append(t)
            elif t=='wn':stack.append((t,stack.pop()))
            else:
                b=stack.pop();a=stack.pop();stack.append((t,a,b))
        if len(stack)!=1:raise ValueError('bad formula expression')
        def emit(tree):
            if isinstance(tree,str):
                return [getattr(self,'par'+str(permutation[int(tree[1:])-1]))()]
            op,*args=tree
            if op=='wn':return [*emit(args[0]),self.wn()]
            primitive='wim' if op=='wa' else 'wal' if op=='wex' else op
            reverse=bool(self.expression_mask&(1<<BINARY.index(primitive)))
            left,right=args
            if not reverse:return [*emit(left),*emit(right),getattr(self,op)()]
            if op in ('wa','wex'):
                return [*emit(right),self.wn(),*emit(left),getattr(self,primitive)(),self.wn()]
            return [*emit(right),*emit(left),getattr(self,op)()]
        return emit(stack[0])

    def axioms(self):
        clauses=super().axioms()
        if self.expression_mask&4:
            clauses[0][2],clauses[0][3]=clauses[0][3],clauses[0][2]
        if self.expression_mask&8:
            clauses[1][1],clauses[1][2]=clauses[1][2],clauses[1][1]
        return clauses


if __name__=='__main__':
    from joint import build_joint,load_recorded
    from machines import count,totalize
    from reduce import reduce
    from register_check import compile_fragment,execute
    config=load_recorded('ics-encoding')
    for mask in range(16):
        m=build_joint(config,sharing=True,compile_machine=False)
        m.__class__=type('ExpressionProbe',(ExpressionOrder,type(m)),{})
        m.expression_mask=mask;m.build_machine()
        print(mask,count(m.tm.states),len(reduce(totalize(m.tm.start,m.tm.states))))
