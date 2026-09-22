"""Execute inference clauses only at their selected counter value.

Every ordinary axiom still uses the eager shared selector. An inference instead
saturating-decrements its selector and touches the formula stack only when the
old counter was one. Then later clauses cannot replace its result and the three
parameters may be consumed. Inferences remain before the protected ordinary
phase, so skipping an unselected intermediate result is harmless.
"""
from machines import require
from TMBuilder import subroutine

class SelectedInference:
    @subroutine
    def when_selected(self,body):
        return [self.label('chosen',[self.axiomcode.decnz,[
            [self.axiomcode.decnz,[self.axiomcode.inc,'break_chosen']],
            body]])]

    @subroutine
    def pop_parameter(self,p):
        return [self.while_decnz(p,()),
                self.unpair(self.scratch1,self.scratch2,self.wffstack),
                self.while_decnz(self.scratch2,self.wffstack.inc),
                self.while_decnz(self.scratch1,p.inc)]

    def axioms(self):
        clauses=super().axioms()
        clauses[0]=[self.when_selected([
            self.pop_parameter(self.param3),self.pop_parameter(self.param2),
            self.while_decnz(self.topwff,()),
            self.while_decnz(self.param3,self.topwff.inc),
            self.par1(),self.wim(),
            self.if_eq(self.topwff,self.param2,
                       self.while_decnz(self.param1,self.topwff.inc))])]
        clauses[1]=[self.when_selected([
            self.pop_parameter(self.param3),
            self.while_decnz(self.topwff,()),
            self.while_decnz(self.param1,self.topwff.inc),
            self.par3(),self.wal()])]
        return clauses


if __name__=='__main__':
    from joint import build_joint,load_recorded
    from machines import count,totalize
    from reduce import reduce
    from register_check import compile_fragment,execute
    config=load_recorded('ics-encoding')
    m=build_joint(config,sharing=True,compile_machine=False)
    m.__class__=type('InferenceProbe',(SelectedInference,type(m)),{})
    code=compile_fragment(m,m.when_selected(m.param1.inc))
    for counter in range(20):
        registers,_=execute(code,{'axiomcode':counter})
        if (registers.get('axiomcode',0),registers.get('param1',0))!=(max(0,counter-1),int(counter==1)):
            raise ValueError('selection guard failed')
    m.build_machine()
    print('raw',count(m.tm.states),'final',len(reduce(totalize(m.tm.start,m.tm.states))))
