"""Combine related axiom schemas before compilation.

Conjoining two schemas with the same parameters preserves their instances up to
propositional reasoning. The optional common-witness POW/UNI formula is taken
from the alternative listed in CatsAreFluffy's source; its equivalence additionally
uses the ability to form a set containing both witnesses (pairing and union).
"""
from storage import TwoScratchICS
from joint import PERMUTATIONS
from ics import LOGICAL, RPN

UP_RPN = ('p2 p3 p2 p2 p3 wel p2 p1 wel wim wal wn '
          'p2 p3 p2 wel p2 p1 wel wa wex wim p3 p2 wel wim wal wex')


class GroupedICS(TwoScratchICS):
    group_b6 = False
    group_pu = 0

    def axioms(self):
        if not hasattr(self, 'layout_order'):
            self.layout_order = self.AXIOMORDER.copy()
        self.AXIOMORDER = self.layout_order.copy()
        clauses = super().axioms()
        first = self.AXIOMORDER[len(LOGICAL)]
        # TwoScratchICS wraps the complete safety phase in these five calls.
        guard = clauses[first][:5]
        clauses[first] = clauses[first][5:]
        dropped = set()
        if self.group_b6:
            clauses[15] = [*clauses[15][:-1], *clauses[16][:-1], self.wa(), self.select()]
            dropped.add(16)
        if self.group_pu:
            if self.group_pu == 1:
                clauses[12] = [*clauses[12][:-1], *clauses[13][:-1], self.wa(), self.select()]
            elif self.group_pu == 2:
                clauses[12] = [*self.constructor_sequence(UP_RPN, PERMUTATIONS[self.protected_permutation]), self.select()]
            else:
                raise ValueError('bad POW/UNI group')
            dropped.add(13)
        self.AXIOMORDER = [i for i in self.layout_order if i not in dropped]
        first = self.AXIOMORDER[len(LOGICAL)]
        clauses[first] = [*guard, *clauses[first]]
        return clauses


if __name__ == '__main__':
    import json
    from pathlib import Path
    from joint import decode
    from machines import count,totalize
    from reduce import reduce
    from joint import load_recorded
    config=load_recorded('ics-storage')
    for b6 in (False,True):
        for pu in (0,1,2):
            m=GroupedICS();m.AXIOMORDER=list(config[0]);m.permutations=config[1];m.protected_permutation=config[2]
            m.group_b6=b6;m.group_pu=pu;m.build_machine()
            print(b6,pu,count(m.tm.states),len(reduce(totalize(m.tm.start,m.tm.states))))
