"""Register-level arithmetic specializations; tested by register_check.py.

Safety compares two registers in place and restores matched decrements from one
scratch counter. A selected detachment may consume its major premise and the
conclusion parameter, because no subsequent clause will use those values.
"""
from ics import ICS
from selected import SelectedICS
from TMBuilder import subroutine


class CompactSafetyICS(ICS):
    safety_mode = 1

    @subroutine
    def safety(self, a, b):
        if not self.safety_mode:
            # Call the original implementation through a distinct helper instance
            # is not valid (node IDs are local); retain its literal body here.
            return [self.while_decnz(a, [self.scratch1.inc,self.scratch2.inc]),
                    self.while_decnz(self.scratch1,a.inc),
                    self.while_decnz(b,[self.scratch1.inc,self.scratch3.inc]),
                    self.while_decnz(self.scratch1,b.inc),
                    self.if_eq(self.scratch2,self.scratch3,a.inc)]
        return [
            self.label('compare', [
                self.label('loop', [a.decnz, [
                    [b.decnz, [self.scratch1.inc, 'continue_loop']],
                    [a.inc, 'break_compare'],
                ]]),
                [[b.decnz, [b.inc, 'break_compare']], a.inc],
            ]),
            self.while_decnz(self.scratch1, [a.inc, b.inc]),
        ]


class OptimizedSelected(SelectedICS, CompactSafetyICS):
    det_mode = 1

    def axioms(self):
        clauses = super().axioms()
        if self.det_mode:
            clauses[0] = [
                self.cparam(self.param3), self.cparam(self.param2),
                self.par3(), self.par1(), self.wim(),
                self.if_eq(self.topwff, self.param2,
                           self.while_decnz(self.param1, self.topwff.inc)),
            ]
        return clauses


if __name__ == '__main__':
    import json
    from pathlib import Path
    from machines import count, totalize
    from reduce import reduce
    from register_check import compile_fragment, execute
    for a in range(20):
        for b in range(20):
            m = CompactSafetyICS()
            regs, _ = execute(compile_fragment(m,m.safety(m.param1,m.param3)), {'param1':a,'param3':b})
            assert regs.get('param1',0)==a+(a==b) and regs.get('param3',0)==b,(a,b,regs)
            assert regs.get('scratch1',0)==0
    print('400 compact safety checks passed')
    from joint import load_recorded
    order=load_recorded('ics-order')[0]
    for cls in (CompactSafetyICS, OptimizedSelected):
        for safety in (0,1):
            for det in ((0,1) if cls is OptimizedSelected else (0,)):
                m=cls();m.safety_mode=safety;m.det_mode=det;m.AXIOMORDER=order;m.build_machine()
                print(cls.__name__,safety,det,count(m.tm.states),len(reduce(totalize(m.tm.start,m.tm.states))))
