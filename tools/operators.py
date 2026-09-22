"""Choose formula-constructor lowering independently for each operator.

Modes 0..3 are four scratch assignments for tagging a payload. Mode 4 fuses a
binary payload construction with tagging. Negation has no binary payload, so
its modes are limited to 0..3. The payload mask controls inner operand order for
=, membership, implication, and forall; outer tags and stack coding never change.
"""
from storage import TwoScratchICS
from TMBuilder import subroutine


class OperatorICS(TwoScratchICS):
    operator_modes = (1, 1, 1, 1, 1)
    payload_mask = 15

    @subroutine
    def tag_config(self, k, mode):
        if mode == 0:
            return [[self.scratch2.inc]*k,
                    self.while_decnz(self.topwff,self.scratch1.inc),
                    self.pair(self.topwff,self.scratch1,self.scratch2)]
        if mode == 1:
            return [[self.scratch1.inc]*k,
                    self.pair(self.scratch2,self.topwff,self.scratch1),
                    self.while_decnz(self.scratch2,self.topwff.inc)]
        if mode == 2:
            return [[self.scratch2.inc]*k,
                    self.pair(self.scratch1,self.topwff,self.scratch2),
                    self.while_decnz(self.scratch1,self.topwff.inc)]
        if mode == 3:
            return [[self.scratch1.inc]*k,
                    self.while_decnz(self.topwff,self.scratch2.inc),
                    self.pair(self.topwff,self.scratch2,self.scratch1)]
        raise ValueError('invalid tag lowering')

    @subroutine
    def payload(self, reversed_order):
        a,b = (self.topwff,self.scratch1) if reversed_order else (self.scratch1,self.topwff)
        return [self.unpair(self.scratch1,self.scratch2,self.wffstack),
                self.while_decnz(self.scratch2,self.wffstack.inc),
                self.pair(self.scratch2,a,b),
                self.while_decnz(self.scratch2,self.topwff.inc)]

    @subroutine
    def operator(self, k):
        mode = self.operator_modes[k]
        if k == 3:
            return self.tag_config(k,mode)
        bit = k if k < 3 else 3
        reverse = bool(self.payload_mask & (1 << bit))
        if mode < 4:
            return [self.payload(reverse),self.tag_config(k,mode)]
        a,b = (self.topwff,self.scratch1) if reverse else (self.scratch1,self.topwff)
        return [self.unpair(self.scratch1,self.scratch2,self.wffstack),
                self.while_decnz(self.scratch2,self.wffstack.inc),
                self.pair(self.scratch2,a,b), [self.scratch1.inc]*k,
                self.pair(self.topwff,self.scratch2,self.scratch1)]

    @subroutine
    def weq(self):return self.operator(0)
    @subroutine
    def wel(self):return self.operator(1)
    @subroutine
    def wim(self):return self.operator(2)
    @subroutine
    def wn(self):return self.operator(3)
    @subroutine
    def wal(self):return self.operator(4)


def build_operators(config,modes,mask=15,sharing=False,grammar=None):
    cls=OperatorICS
    if sharing:
        from stack_ops import SharedCopy,SharedPair,SharedPop
        cls=type("SharedOperators",(SharedCopy,SharedPair,SharedPop,cls),{})
    if grammar is not None:
        from grammar import GrammarCompiler
        cls=type("FactoredOperators",(GrammarCompiler,cls),{})
    m=cls();m.grammar_options=grammar;m.AXIOMORDER=list(config[0]);m.permutations=config[1];m.protected_permutation=config[2]
    m.operator_modes=tuple(modes);m.payload_mask=mask;m.build_machine()
    return m


if __name__ == '__main__':
    import json
    from pathlib import Path
    from joint import decode
    from machines import count,totalize
    from reduce import reduce
    from joint import load_recorded
    config=load_recorded('ics-encoding')
    for mask in range(16):
        m=build_operators(config,(1,1,1,1,1),mask)
        print(mask,count(m.tm.states),len(reduce(totalize(m.tm.start,m.tm.states))))
