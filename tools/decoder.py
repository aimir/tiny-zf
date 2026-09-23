"""Proof-field decoding with phase-local register allocation.

The planner tracks zero, dead and live values. Its emitted program uses only
the existing destructive Cantor unpair and transfer kernels. At the boundary
all fields and the proof tail occupy their original logical registers, and
both scratch registers are zero. The theorem stack and counter are untouched.
"""
from machines import require
from TMBuilder import subroutine

FIELDS = ('axiomcode','param1','param2','param3')
REGS = ('scratch1','scratch2','prooflist',*FIELDS)


def default_options():
    return {'order':list(FIELDS), 'clear_order':list(FIELDS), 'eager':True,
            'stages':[['scratch1','scratch2',False] for _ in range(4)], 'defer_heads':False}


def allocation_plan(options):
    order=options.get('order',FIELDS)
    require(sorted(order)==sorted(FIELDS),'bad proof-field order')
    clear_order=options.get('clear_order',FIELDS)
    require(sorted(clear_order)==sorted(FIELDS),'bad clear order')
    stages=options.get('stages',default_options()['stages'])
    require(len(stages)==4,'decoder needs four stages')
    values={r:('dead' if r in FIELDS else 'zero') for r in REGS}
    values['prooflist']='tail'
    ops=[]; bindings={}

    def clear(r):
        require(values[r] in ('zero','dead'),'clear would destroy a live value')
        if values[r]=='dead':ops.append(('clear',r));values[r]='zero'

    def move(a,b):
        if a==b:return
        clear(b);ops.append(('move',a,b));values[b]=values[a];values[a]='zero'

    if options.get('eager',True):
        for r in clear_order:clear(r)
    current='prooflist'
    for dest,(head_choice,tail_choice,head_first) in zip(order,stages):
        available=[r for r in REGS if r!=current and values[r] in ('zero','dead')]
        # Choices may name a preferred register or index the legal alternatives.
        def choose(choice,available):
            if isinstance(choice,str):
                require(choice in available,f'unavailable decoding register {choice}')
                return choice
            require(type(choice)==int and choice>=0,'bad allocation choice')
            return available[choice%len(available)]
        head=choose(head_choice,available)
        tails=[r for r in available if r!=head and (options.get('defer_heads',False) or r!=dest)]
        tail=choose(tail_choice,tails)
        clear(head);clear(tail)
        ops.append(('unpair',head,tail,current))
        values[current]='zero';values[head]=dest;values[tail]='tail'
        # The ordinary mode places the field immediately. Deferred mode keeps
        # the result where it landed, moving all four fields only at the end.
        if options.get('defer_heads',False):
            bindings[dest]=head;current=tail
        else:
            def place_head():move(head,dest)
            def place_tail():
                nonlocal current
                # A stage can return the tail to the common input, or leave it
                # where unpair produced it for the next stage.
                target='prooflist' if options.get('restore_tail',True) else tail
                require(target!=head or head_first,'tail overwrites extracted field')
                move(tail,target);current=target
            if head_first:place_head();place_tail()
            else:place_tail();place_head()
            bindings[dest]=dest
    # Parallel assignment: evacuate cycles through a known-zero free register.
    targets={**bindings,'prooflist':current}
    while any(dst!=src for dst,src in targets.items()):
        sources=set(targets.values())
        choices=[(d,s) for d,s in targets.items() if d!=s and d not in sources]
        if choices:
            dst,src=choices[0];move(src,dst);targets[dst]=dst
        else:
            dst,src=next((d,s) for d,s in targets.items() if d!=s)
            spare=next(r for r in REGS if r not in sources and values[r] in ('zero','dead'))
            move(src,spare);targets[dst]=spare
    require(all(values[r]==r for r in FIELDS),'field assignment mismatch')
    require(values['prooflist']=='tail','lost remainder')
    require(values['scratch1']==values['scratch2']=='zero','scratch not cleared')
    return ops


class AllocatedDecoder:
    def decoder_prefix(self):
        out=[]
        def reg(name):
            return self.wffstack if name=='prooflist' and self.decoder_options.get('borrow_stack',False) else getattr(self,name)
        for op in allocation_plan(self.decoder_options):
            if op[0]=='clear':out.append(self.while_decnz(reg(op[1]),()))
            elif op[0]=='move':out.append(self.while_decnz(reg(op[1]),reg(op[2]).inc))
            else:out.append(self.unpair(*(reg(r) for r in op[1:])))
        return out

    def enumeration_prefix(self):
        return self.if_not_decnz(self.prooflist,[
            self.while_decnz(self.nextproof,[self.scratch1.inc,self.prooflist.inc]),
            self.while_decnz(self.scratch1,self.nextproof.inc),self.nextproof.inc])

    @subroutine
    def main(self):
        clauses=self.axioms()
        enumeration=self.enumeration_prefix();decoder=self.decoder_prefix()
        before=[];after=[]
        if self.decoder_options.get('borrow_stack',False):
            before=[self.v_0(),self.while_decnz(self.wffstack,self.topwff.inc),
                    self.while_decnz(self.prooflist,self.wffstack.inc)]
            after=[self.while_decnz(self.wffstack,self.prooflist.inc),
                   self.while_decnz(self.topwff,self.wffstack.inc)]
        suffix=[*([] if before else [self.v_0()]),
                *[clause for i in self.AXIOMORDER for clause in clauses[i]],
                [self.topwff.decnz,self.label('if',[
                    [self.topwff.decnz,[[self.topwff.inc,self.topwff.inc],'break_if']],
                    'halt'])]]
        self.decoder_sections=(enumeration,[*before,*decoder,*after],suffix)
        return [enumeration,*before,*decoder,*after,*suffix]


class PackedCounter(AllocatedDecoder):
    """P stores Cantor(next counter, remaining proof) between iterations.

Push the old theorem before unpacking. Its cleared top register holds the
counter through decoding; repack before constructing clauses. All operations
reuse existing three-register kernels. The dedicated nextproof slot disappears.
"""
    @subroutine
    def main(self):
        clauses=self.axioms()
        before=[self.v_0(),self.unpair(self.scratch1,self.scratch2,self.prooflist),
                self.while_decnz(self.scratch1,self.topwff.inc),
                self.while_decnz(self.scratch2,self.prooflist.inc)]
        enumeration=self.enumeration_prefix();decoder=self.decoder_prefix()
        after=[self.while_decnz(self.prooflist,self.scratch1.inc),
               self.pair(self.scratch2,self.topwff,self.scratch1),
               self.while_decnz(self.scratch2,self.prooflist.inc)]
        suffix=[*[clause for i in self.AXIOMORDER for clause in clauses[i]],
                [self.topwff.decnz,self.label('if',[
                    [self.topwff.decnz,[[self.topwff.inc,self.topwff.inc],'break_if']],
                    'halt'])]]
        self.decoder_sections=(before,[enumeration,*decoder,*after],suffix)
        return [*before,enumeration,*decoder,*after,*suffix]


def apply_decoder(machine, options):
    machine.decoder_options=options
    packed=machine.decoder_options.get('packed_counter',False)
    require(not(packed and machine.decoder_options.get('borrow_stack',False)), 'conflicting top-register uses')
    machine.__class__=type('DecoderICS',(PackedCounter if packed else AllocatedDecoder,type(machine)),{})
    if packed:
        # Regenerate the physical selector chains without the unused counter.
        import tm
        machine.tm=tm.TuringMachine();machine.registers={};machine.nextreg=0;machine.prevreg=None
        for name in ('prooflist','topwff','wffstack',*FIELDS,'scratch1','scratch2','scratch3'):
            setattr(machine,name,machine.reg(name))
        machine.nextproof=machine.topwff
    return machine


def build_decoder(record, *, compile_machine=True):
    from joint import build_joint,decode
    return build_joint(decode(record),sharing=record.get('shared_operations',False),
                       grammar=record.get('grammar'),formula_choices=record.get('formula_choices'),
                       decoder=record.get('decoder',default_options()),compile_machine=compile_machine)
