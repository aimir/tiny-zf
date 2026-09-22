"""Experimental fused formula constructors for the ICS program.

The payload is paired with a small tag directly, avoiding a temporary push of
that tag to the formula stack followed by its immediate pop.
"""
from ics import ICS
from TMBuilder import subroutine


class FusedICS(ICS):
    tag_mode = 0
    binary_mode = 0

    @subroutine
    def tag(self, k):
        if self.tag_mode == 0:
            return [([self.scratch2.inc] * k),
                    self.while_decnz(self.topwff, self.scratch1.inc),
                    self.pair(self.topwff, self.scratch1, self.scratch2)]
        if self.tag_mode == 1:
            return [([self.scratch1.inc] * k),
                    self.pair(self.scratch2, self.topwff, self.scratch1),
                    self.while_decnz(self.scratch2, self.topwff.inc)]
        if self.tag_mode == 2:
            return [([self.scratch2.inc] * k),
                    self.pair(self.scratch1, self.topwff, self.scratch2),
                    self.while_decnz(self.scratch1, self.topwff.inc)]
        if self.tag_mode == 3:
            return [([self.scratch1.inc] * k),
                    self.while_decnz(self.topwff, self.scratch2.inc),
                    self.pair(self.topwff, self.scratch2, self.scratch1)]
        raise ValueError('unknown tag mode')

    @subroutine
    def binary(self, k):
        if not self.binary_mode:
            return [self.cons(), self.tag(k)]
        return [self.unpair(self.scratch1, self.scratch2, self.wffstack),
                self.while_decnz(self.scratch2, self.wffstack.inc),
                self.pair(self.scratch2, self.scratch1, self.topwff),
                ([self.scratch1.inc] * k),
                self.pair(self.topwff, self.scratch2, self.scratch1)]

    @subroutine
    def weq(self):
        return self.binary(0)

    @subroutine
    def wel(self):
        return self.binary(1)

    @subroutine
    def wim(self):
        return self.binary(2)

    @subroutine
    def wn(self):
        return self.tag(3)

    @subroutine
    def wal(self):
        return self.binary(4)


if __name__ == '__main__':
    import json
    from pathlib import Path
    from machines import count, totalize
    from reduce import reduce
    from joint import load_recorded
    order = load_recorded('ics-order')[0]
    for tag in range(4):
        for binary in range(2):
            m = FusedICS();m.tag_mode = tag;m.binary_mode = binary;m.AXIOMORDER = order;m.build_machine()
            print(tag, binary, count(m.tm.states), len(reduce(totalize(m.tm.start, m.tm.states))))
