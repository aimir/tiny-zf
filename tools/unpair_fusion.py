"""Fused Cantor unpair/tail restoration and a native diagonal-step kernel.

The tape kernel operates on the two rightmost registers A, B. It implements
(A,B) -> (A+1,B-1) for B>0, otherwise (0,A+1). All other registers survive.
"""
from machines import require
from TMBuilder import subroutine
from native import build_native
import tm

CANTOR_STEP='''
1.cstep 0 1 R 1.cstep.gap
1.cstep.gap 0 0 R 1.cstep.gap
1.cstep.gap 1 0 R 1.cstep.prefix
1.cstep.prefix 1 1 R 1.cstep.prefix
1.cstep.prefix 0 1 R 1.cstep.separator
1.cstep.separator 1 0 R 1.cstep.prefix
1.cstep.separator 0 0 R 1.cstep.first
1.cstep.first 1 1 R 1.cstep.second
1.cstep.second 1 1 R 1.cstep.end
1.cstep.second 0 1 R 1.cstep.end
1.cstep.end 1 1 R 1.cstep.end
1.cstep.end 0 1 L 1.sel
'''


def options(machine):return machine.native_options.get('unpair',{})


def step_contract(a,b):
    return (f'3.{a}.inc',((f'3.{b}.decnz','_break.1'),(f'3.{a}.decnz',(f'3.{b}.inc','_continue.2'))))


class FusedUnpair:
    def loop_body(self,a,b):
        o=options(self)
        if (o.get('step') or o.get('inline_step')) and [str(a),str(b)]==o['step_pair']:
            return [f'3.{b}.cstep' if o.get('step') else step_contract(a,b),'continue_loop']
        variant=o.get('variant',0)
        if variant==0:
            return [a.inc,[[b.decnz,'continue_loop'],[self.while_decnz(a,b.inc),'continue_loop']]]
        if variant in (1,2):
            tail=[self.while_decnz(a,b.inc),b.inc] if variant==1 else [b.inc,self.while_decnz(a,b.inc)]
            return [[b.decnz,[a.inc,'continue_loop']],[tail[0],[tail[1],'continue_loop']]]
        return [a.inc,[self.if_not_decnz(b,self.while_decnz(a,b.inc)),'continue_loop']]

    @subroutine
    def unpair(self,a,b,n):
        require(len({str(a),str(b),str(n)})==3,'unpair registers must be distinct')
        return [self.label('loop',[n.decnz,self.loop_body(a,b)])]

    @subroutine
    def unpair_restore(self,a,b,n):
        require(len({str(a),str(b),str(n)})==3,'unpair registers must be distinct')
        return [self.label('loop',[[n.decnz,self.loop_body(a,b)],self.while_decnz(b,n.inc)])]

    def decoder_prefix(self):
        if not options(self).get('restore',0)&1:return super().decoder_prefix()
        from decoder import allocation_plan
        ops=allocation_plan(self.decoder_options);out=[];i=0
        def reg(name):return self.wffstack if name=='prooflist' and self.decoder_options.get('borrow_stack',False) else getattr(self,name)
        while i<len(ops):
            op=ops[i]
            if op[0]=='unpair' and i+1<len(ops) and ops[i+1]==('move',op[2],op[3]):
                out.append(self.unpair_restore(*(reg(r) for r in op[1:])));i+=2;continue
            if op[0]=='clear':out.append(self.while_decnz(reg(op[1]),()))
            elif op[0]=='move':out.append(self.while_decnz(reg(op[1]),reg(op[2]).inc))
            else:out.append(self.unpair(*(reg(r) for r in op[1:])))
            i+=1
        return out

    @subroutine
    def select(self):
        if not options(self).get('restore',0)&2:return super().select()
        return [self.unpair_restore(self.scratch1,self.scratch2,self.wffstack),
                self.if_not_decnz(self.axiomcode,[self.while_decnz(self.topwff,()),self.while_decnz(self.scratch1,self.topwff.inc)]),
                self.while_decnz(self.scratch1,())]

    def axioms(self):
        clauses=super().axioms()
        if options(self).get('restore',0)&4:
            from ics import LOGICAL
            first=self.AXIOMORDER[len(LOGICAL)]
            clauses[first][3:5]=[self.unpair_restore(self.scratch1,self.scratch2,self.wffstack)]
        return clauses

    def generate(self):
        super().generate()
        if options(self).get('step'):
            for line in CANTOR_STEP.splitlines():self.tm.loadline(line,'<Cantor step>',0)
            a,b=options(self)['step_pair']
            for name,target in ((a,'1.cstep'),(b,f'3.{a}.cstep')):
                self.tm.states[(f'3.{name}.cstep','0')]=tm.Transition('0','R','1.sel')
                self.tm.states[(f'3.{name}.cstep','1')]=tm.Transition('1','R',target)


def apply_unpair(machine,record):
    o=record['unpair']
    require(o.get('variant',0) in range(4),'unknown unpair variant')
    require(hasattr(machine,'decoder_options'),'unpair fusion requires the allocated decoder')
    if o.get('step'):
        pair=o.get('step_pair',['scratch1','scratch2'])
        require(list(machine.registers)[:2]==pair,'native Cantor outputs must be the two rightmost registers')
        o['step_pair']=pair;a,b=pair;leaf=f'3.{b}.cstep'
        machine.registers.native_primitives.add(leaf)
        machine.native_expansions[leaf]=step_contract(a,b)
    require(type(o.get('restore',0)) is int and o.get('restore',0) in range(8),'bad restoration mask')
    machine.__class__=type('FusedUnpairICS',(FusedUnpair,type(machine)),{})
    if o.get('contract_only'):
        machine.__class__=type('ContractUnpairICS',(ContractUnpair,type(machine)),{})
    return machine


class ContractUnpair:
    """Expand fused calls into the original contract for the source-level audit."""
    def unpair(self,a,b,n):
        from TMBuilder import TMBuilder
        return TMBuilder.unpair(self,a,b,n)

    def unpair_restore(self,a,b,n):
        return [self.unpair(a,b,n),self.while_decnz(b,n.inc)]


def build_contract(record,*,compile_machine=False):
    from copy import deepcopy
    r=deepcopy(record);r['native']['unpair']['contract_only']=True
    return build_native(r,compile_machine=compile_machine)


def expand_native_tree(record,data):
    """Expand optimized tape primitives, preserving the surrounding tree."""
    from copy import deepcopy
    from functools import lru_cache
    from instruction_tree import Trees
    machine=build_native(record,compile_machine=False)
    arena=Trees();root=arena.import_record(data,machine.registers)
    @lru_cache(None)
    def visit(v):
        if isinstance(v,str):return contract(machine.native_expansions[v]) if v in machine.native_expansions else v
        a,b=arena.nodes[v];return arena.node(visit(a),visit(b))
    def contract(v):
        if isinstance(v,str):return visit(v)
        return arena.node(contract(v[0]),contract(v[1]))
    tree=arena.export(visit(root));arena.clear_caches()
    result=deepcopy(record);result['native']['moves']=[]
    u=result['native'].get('unpair')
    if u and u.get('step'):u['step']=False;u['inline_step']=True
    return result,tree
