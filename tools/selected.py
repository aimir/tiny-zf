"""Execute only the selected axiom/inference body, then discard its dummy entry.

The upstream program constructs every axiom and selects a result afterward.
Here a structured decision chain first consumes the selector. Parameter loading
is unconditional inside a selected inference, and parameter safety is local to
the selected protected schema. Selector zero denotes the first clause, with the
last clause also handling selectors beyond the explicit range.
"""
from ics import ICS, LABELS, PROTECTED, ORIGINAL, LOGICAL, RPN
from machines import ZF2, require
from TMBuilder import subroutine


class SelectedICS(ICS):
    @subroutine
    def cparam(self, p):
        return [self.while_decnz(p, ()),
                self.unpair(self.scratch1, self.scratch2, self.wffstack),
                self.while_decnz(self.scratch2, self.wffstack.inc),
                self.while_decnz(self.scratch1, p.inc)]

    def select(self):
        return ()

    def axioms(self):
        original = ZF2.axioms(self)
        clauses = [original[ORIGINAL[name]] for name in LOGICAL]
        for name in PROTECTED:
            sequence = [getattr(self, 'par' + token[1:] if token.startswith('p') else token)()
                        for token in RPN[name].split()]
            clauses.append([self.safety(self.param1, self.param3),
                            self.safety(self.param2, self.param3), *sequence])
        return clauses

    def decision(self, bodies):
        if len(bodies) == 1:
            return bodies[0]
        return self.label('choose', [
            [self.axiomcode.decnz, [self.decision(bodies[1:]), 'break_choose']],
            bodies[0],
        ])

    @subroutine
    def halt_if_one(self):
        return [[self.topwff.decnz,
                 self.label('if', [
                     [self.topwff.decnz,
                      [[self.topwff.inc, self.topwff.inc], 'break_if']],
                     'halt',
                 ])]]

    @subroutine
    def main(self):
        require(len(self.AXIOMORDER) == len(LABELS) and set(self.AXIOMORDER) == set(range(len(LABELS))),
                'incomplete selected ICS order')
        clauses = self.axioms()
        decoding = []
        for target in (self.axiomcode, self.param1, self.param2, self.param3):
            decoding += [self.while_decnz(target, ()),
                         self.unpair(self.scratch1, self.scratch2, self.prooflist),
                         self.while_decnz(self.scratch2, self.prooflist.inc),
                         self.while_decnz(self.scratch1, target.inc)]
        return [
            self.if_not_decnz(self.prooflist, [
                self.while_decnz(self.nextproof, [self.scratch1.inc, self.prooflist.inc]),
                self.while_decnz(self.scratch1, self.nextproof.inc), self.nextproof.inc]),
            *decoding,
            self.pushwff(),
            self.decision([clauses[i] for i in self.AXIOMORDER]),
            # Formula construction leaves the initial zero just below its result.
            self.unpair(self.scratch1, self.scratch2, self.wffstack),
            self.while_decnz(self.scratch2, self.wffstack.inc),
            self.halt_if_one(),
        ]


if __name__ == '__main__':
    from machines import count, totalize
    from reduce import reduce
    m = SelectedICS();m.build_machine()
    print('raw', count(m.tm.states), 'final', len(reduce(totalize(m.tm.start, m.tm.states))))
