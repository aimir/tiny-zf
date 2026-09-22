"""Reuse the formula-top register as comparison scratch, spilling it once.

The guard phase saves the current theorem on the existing formula stack. Both
safety comparisons can then share topwff as a zero-initialized scratch register;
the theorem is restored before constructing any protected formula. Detachment
already has topwff free at its equality test. Thus scratch3 becomes unreachable.
"""
from joint import PermutedICS
from ics import LOGICAL
from TMBuilder import subroutine


class TwoScratchICS(PermutedICS):
    @subroutine
    def safety(self, a, b):
        return [self.while_decnz(a, [self.scratch1.inc, self.scratch2.inc]),
                self.while_decnz(self.scratch1, a.inc),
                self.while_decnz(b, [self.scratch1.inc, self.topwff.inc]),
                self.while_decnz(self.scratch1, b.inc),
                self.if_eq(self.scratch2, self.topwff, a.inc)]

    def axioms(self):
        clauses = super().axioms()
        clauses[0] = [
            self.cparam(self.param3), self.cparam(self.param2),
            self.par3(), self.par1(), self.wim(),
            self.while_decnz(self.topwff, self.scratch2.inc),
            self.while_decnz(self.param2, [self.scratch1.inc, self.topwff.inc]),
            self.while_decnz(self.scratch1, self.param2.inc),
            self.if_eq(self.scratch2, self.topwff, [
                self.while_decnz(self.param1, [self.scratch1.inc, self.topwff.inc]),
                self.while_decnz(self.scratch1, self.param1.inc)]),
            self.select(),
        ]
        first = self.AXIOMORDER[len(LOGICAL)]
        guard1, guard2, *body = clauses[first]
        clauses[first] = [self.pushwff(), guard1, guard2,
                          self.unpair(self.topwff, self.scratch2, self.wffstack),
                          self.while_decnz(self.scratch2, self.wffstack.inc), *body]
        return clauses


if __name__ == '__main__':
    import json
    from pathlib import Path
    from joint import decode
    from machines import count,totalize
    from reduce import reduce
    from joint import load_recorded
    config=load_recorded('ics-joint')
    m=TwoScratchICS();m.AXIOMORDER=list(config[0]);m.permutations=config[1];m.protected_permutation=config[2];m.build_machine()
    print('raw',count(m.tm.states),'final',len(reduce(totalize(m.tm.start,m.tm.states))))
    print('scratch3 used?', any('scratch3' in q for q,b in m.tm.states))
