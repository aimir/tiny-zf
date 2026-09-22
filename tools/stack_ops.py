"""Share pairing, stack selection and copies without changing register results.

Each routine assumes scratch1/scratch2 start at zero and restores them to zero.
The formula and proof encodings and the selected theorem are unchanged.
"""
from ics import LOGICAL
from TMBuilder import subroutine


class SharedPop:
    """Pop through the common scratch pair, keeping the candidate in topwff."""
    @subroutine
    def select(self):
        return [self.unpair(self.scratch1,self.scratch2,self.wffstack),
                self.while_decnz(self.scratch2,self.wffstack.inc),
                self.if_not_decnz(self.axiomcode,[
                    self.while_decnz(self.topwff,()),
                    self.while_decnz(self.scratch1,self.topwff.inc)]),
                self.while_decnz(self.scratch1,())]

    def axioms(self):
        clauses=super().axioms()
        first=self.AXIOMORDER[len(LOGICAL)]
        push,g1,g2,unpair,restore,*body=clauses[first]
        clauses[first]=[push,g1,g2,
            self.unpair(self.scratch1,self.scratch2,self.wffstack),restore,
            self.while_decnz(self.scratch1,self.topwff.inc),*body]
        return clauses


class SharedPair:
    """Push P(topwff, wffstack) through the existing constructor pairing call."""
    @subroutine
    def pushwff(self):
        return [self.while_decnz(self.wffstack,self.scratch1.inc),
                self.pair(self.scratch2,self.topwff,self.scratch1),
                self.while_decnz(self.scratch2,self.wffstack.inc)]


class SharedCopy:
    """Order independent increments to reuse comparison-copy instruction nodes."""
    @subroutine
    def par1(self):
        return [self.pushwff(),
                self.while_decnz(self.param1,[self.scratch1.inc,self.topwff.inc]),
                self.while_decnz(self.scratch1,self.param1.inc)]

    @subroutine
    def par2(self):
        return [self.pushwff(),
                self.while_decnz(self.param2,[self.scratch1.inc,self.topwff.inc]),
                self.while_decnz(self.scratch1,self.param2.inc)]

    @subroutine
    def par3(self):
        return [self.pushwff(),
                self.while_decnz(self.param3,[self.scratch1.inc,self.topwff.inc]),
                self.while_decnz(self.scratch1,self.param3.inc)]
