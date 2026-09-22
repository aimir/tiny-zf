"""Experimental port of the corrected CatsAreFluffy ICS axiomatization.

The predicate calculus uses Wade's implementations. The protected final phase
uses the exact constructor sequences from CatsAreFluffy 74a0e04, with parameter
safety applied before that phase. No theorem of equiconsistency is claimed here.
"""
from machines import ZF2, require
from TMBuilder import subroutine

LOGICAL = ('DET', 'GEN', 'B1', 'B2', 'B3', 'B4', 'B6b', 'B6c', 'B7', 'B8a', 'B8b', 'B8c')
PROTECTED = ('POW', 'UNI', 'ICS', 'B6a1', 'B6a2')
LABELS = LOGICAL + PROTECTED
ORIGINAL = dict(zip(LOGICAL, (0, 1, 2, 3, 4, 5, 9, 10, 11, 12, 13, 14)))
RPN = {
 'POW': 'p2 p3 p2 p2 p3 wel p2 p1 wel wim wal p3 p2 wel wim wal wex',
 'UNI': 'p2 p3 p2 p3 p2 wel p2 p1 wel wa wex p3 p2 wel wim wal wex',
 'ICS': ('p2 p3 p3 p1 wel p1 p2 wex p3 p2 wel wim wim '
         'p3 p2 wel p1 p2 wex wim wa '
         'wal p1 p1 p2 wel p3 p2 '
         'p3 p3 p2 wel p2 wa wex wim wal wim wal wa wex'),
 'B6a1': 'p1 p2 weq p3 p1 p2 weq wal wim',
 'B6a2': 'p1 p2 wel p3 p1 p2 wel wal wim',
}


def validate_ics_order(order):
    require(len(order) == len(LABELS) and set(order) == set(range(len(LABELS))), 'invalid ICS order')
    require(set(order[:len(LOGICAL)]) == set(range(len(LOGICAL))), 'unsafe interleaving of safety phases')


class ICS(ZF2):
    def __init__(self):
        super().__init__()
        self.AXIOMORDER = list(range(len(LABELS)))

    @subroutine
    def safety(self, a, b):
        return [
            self.while_decnz(a, [self.scratch1.inc, self.scratch2.inc]),
            self.while_decnz(self.scratch1, a.inc),
            self.while_decnz(b, [self.scratch1.inc, self.scratch3.inc]),
            self.while_decnz(self.scratch1, b.inc),
            self.if_eq(self.scratch2, self.scratch3, a.inc),
        ]

    def axioms(self):
        validate_ics_order(self.AXIOMORDER)
        original = super().axioms()
        clauses = [original[ORIGINAL[name]] for name in LOGICAL]
        for name in PROTECTED:
            sequence = [getattr(self, 'par' + token[1:] if token.startswith('p') else token)()
                        for token in RPN[name].split()]
            clauses.append([*sequence, self.select()])
        first = self.AXIOMORDER[len(LOGICAL)]
        clauses[first] = [self.safety(self.param1, self.param3),
                          self.safety(self.param2, self.param3), *clauses[first]]
        return clauses


def build_ics(order=None):
    machine = ICS()
    if order is not None:
        machine.AXIOMORDER = list(order)
    machine.build_machine()
    return machine


if __name__ == '__main__':
    from machines import count, totalize
    from reduce import reduce
    machine = build_ics()
    print('raw', count(machine.tm.states), 'final', len(reduce(totalize(machine.tm.start, machine.tm.states))))
