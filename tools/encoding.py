"""Alternative formula coding: reverse the operands inside binary payload pairs.

The outer tag pair is unchanged. Hence equality(v0,v0) remains code 0 and
membership(v0,v0) remains code 1. Formula-stack pairs retain the original order.
All constructors use the same new payload convention, so this is an injective
recoding of formula trees, not a change to the formulas emitted by the schemas.
"""
from constructors import FusedICS
from storage import TwoScratchICS
from TMBuilder import subroutine


class ReversedFusion(FusedICS):
    @subroutine
    def cons(self):
        return [self.unpair(self.scratch1, self.scratch2, self.wffstack),
                self.while_decnz(self.scratch2, self.wffstack.inc),
                self.pair(self.scratch2, self.topwff, self.scratch1),
                self.while_decnz(self.scratch2, self.topwff.inc)]

    @subroutine
    def binary(self, k):
        if not self.binary_mode:
            return [self.cons(), self.tag(k)]
        return [self.unpair(self.scratch1, self.scratch2, self.wffstack),
                self.while_decnz(self.scratch2, self.wffstack.inc),
                self.pair(self.scratch2, self.topwff, self.scratch1),
                [self.scratch1.inc] * k,
                self.pair(self.topwff, self.scratch2, self.scratch1)]


class ReversedTwoScratch(ReversedFusion, TwoScratchICS):
    pass


if __name__ == '__main__':
    import json
    from pathlib import Path
    from joint import decode
    from machines import count, totalize
    from reduce import reduce
    from joint import load_recorded
    config=load_recorded('ics-storage')
    for fusion in range(8):
        m=ReversedTwoScratch();m.AXIOMORDER=list(config[0]);m.permutations=config[1];m.protected_permutation=config[2]
        m.tag_mode=fusion//2;m.binary_mode=fusion%2;m.build_machine()
        print(fusion,count(m.tm.states),len(reduce(totalize(m.tm.start,m.tm.states))))
