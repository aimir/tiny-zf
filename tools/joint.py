"""Joint source/layout experiments for ICS, preserving each logical axiom schema.

Independent parameter permutations are bijections of each schema's instances.
The five protected schemas share one permutation, with their safety guard
renamed consistently. Fused constructor choices change arithmetic lowering only.
"""
import itertools
from ics import ICS, LOGICAL, PROTECTED, RPN, ORIGINAL, validate_ics_order
from constructors import FusedICS
from machines import ZF2, require

PERMUTATIONS = tuple(itertools.permutations((1, 2, 3)))
SCHEMAS = LOGICAL[2:]
LOGIC_RPN = {
 'B1': 'p1 p2 wim p2 p3 wim p1 p3 wim wim wim',
 'B2': 'p1 wn p1 wim p1 wim',
 'B3': 'p1 p1 wn p2 wim wim',
 'B4': 'p1 p2 p3 wim wal p1 p2 wal p1 p3 wal wim wim',
 'B6b': 'p1 p2 p3 wal wal p2 p1 p3 wal wal wim',
 'B6c': 'p1 p1 p2 wal wex p2 wim',
 'B7': 'p1 p1 p2 weq wex',
 'B8a': 'p1 p2 weq p1 p3 weq p2 p3 weq wim wim',
 'B8b': 'p1 p2 weq p1 p3 wel p2 p3 wel wim wim',
 'B8c': 'p1 p2 weq p3 p1 wel p3 p2 wel wim wim',
}


class PermutedICS(ICS):
    permutations = (0,) * len(SCHEMAS)
    protected_permutation = 0

    def constructor_sequence(self, source, permutation):
        methods = []
        for token in source.split():
            name = 'par' + str(permutation[int(token[1:])-1]) if token.startswith('p') else token
            methods.append(getattr(self, name)())
        return methods

    def axioms(self):
        validate_ics_order(self.AXIOMORDER)
        original = ZF2.axioms(self)
        clauses = [original[0], original[1]]
        for name, permutation in zip(SCHEMAS, self.permutations):
            clauses.append([*self.constructor_sequence(LOGIC_RPN[name], PERMUTATIONS[permutation]), self.select()])
        permutation = PERMUTATIONS[self.protected_permutation]
        for name in PROTECTED:
            clauses.append([*self.constructor_sequence(RPN[name], permutation), self.select()])
        p1, p2, p3 = (getattr(self, 'param' + str(i)) for i in permutation)
        first = self.AXIOMORDER[len(LOGICAL)]
        clauses[first] = [self.safety(p1, p3), self.safety(p2, p3), *clauses[first]]
        return clauses


class FusedPermutedICS(FusedICS, PermutedICS):
    pass


def build_joint(config, sharing=False, grammar=None, compile_machine=True, formula_choices=None, instruction_tree=None, decoder=None):
    order, permutations, protected, fusion, storage, reverse = config
    require(len(permutations) == len(SCHEMAS) and all(i in range(6) for i in permutations), 'bad parameter permutation')
    require(protected in range(6) and fusion in range(-1, 8), 'bad lowering configuration')
    if reverse:
        require(fusion >= 0, 'reversed payloads require explicit tag constructors')
        from encoding import ReversedFusion, ReversedTwoScratch
        if storage:
            machine = ReversedTwoScratch()
        else:
            class ReversedPermuted(ReversedFusion, PermutedICS):
                pass
            machine = ReversedPermuted()
    elif storage:
        from storage import TwoScratchICS
        if fusion == -1:
            machine = TwoScratchICS()
        else:
            class FusedTwoScratch(FusedICS, TwoScratchICS):
                pass
            machine = FusedTwoScratch()
    else:
        machine = PermutedICS() if fusion == -1 else FusedPermutedICS()
    if sharing:
        require(storage, "shared stack operations require the two-scratch source")
        from stack_ops import SharedCopy, SharedPair, SharedPop
        cls = type("SharedICS", (SharedCopy, SharedPair, SharedPop, type(machine)), {})
        machine = cls()
    if grammar is not None:
        from grammar import GrammarCompiler
        cls = type("FactoredICS", (GrammarCompiler, type(machine)), {})
        machine = cls()
        machine.grammar_options = grammar
    if formula_choices is not None:
        from formula_rewrite import RewrittenFormulas, validate_choices
        validate_choices(formula_choices)
        cls = type("RewrittenICS", (RewrittenFormulas, type(machine)), {})
        machine.__class__ = cls
        machine.rewrite_choices = dict(formula_choices)
    if decoder is not None:
        from decoder import apply_decoder
        machine=apply_decoder(machine,decoder)
    if instruction_tree is not None:
        from instruction_tree import TreeCompiler
        cls = type("TreeICS", (TreeCompiler, type(machine)), {})
        machine.__class__ = cls
        machine.instruction_tree_record = instruction_tree
    machine.AXIOMORDER = list(order)
    machine.permutations = tuple(permutations)
    machine.protected_permutation = protected
    if fusion != -1:
        machine.tag_mode = fusion // 2
        machine.binary_mode = fusion % 2
    if compile_machine:
        machine.build_machine()
    return machine


def encode(config):
    order, permutations, protected, fusion, storage, reverse = config
    return {'order': list(order), 'parameter_permutations': dict(zip(SCHEMAS, permutations)),
            'protected_permutation': protected, 'fusion': fusion, 'two_scratch': storage, 'reverse_payload': reverse}


def decode(config):
    return (tuple(config['order']), tuple(config.get('parameter_permutations', {}).get(name, 0) for name in SCHEMAS),
            config.get('protected_permutation', 0), config.get('fusion', -1), config.get('two_scratch', False), config.get('reverse_payload', False))


def load_recorded(name='ics-encoding'):
    """Load a curated checkpoint without relying on untracked search files."""
    import json
    from machines import ROOT
    records=json.loads((ROOT/'reference/ics-experiments.json').read_text())['runs']
    record=next(r for r in records if r['id']==name)
    return decode(record.get('best',record['initial']))
