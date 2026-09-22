"""Formula identities, deliberately invalid rewrites, and compiler integration."""
import json
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
from formula_rewrite import LIMITS, check_rewrite, parse, rewrite, validate_choices
from grammar import equivalent_cfg
from ics import RPN
from joint import build_joint, decode
from machines import ROOT
from register_check import compile_fragment
from verify_sharing import grammar_check


class FormulaRewriteTests(unittest.TestCase):
    def test_all_generated_choices_pass_independent_checker(self):
        checked = 0
        for name, limit in LIMITS.items():
            for choice in range(limit):
                check_rewrite(RPN[name], rewrite(RPN[name], choice))
                checked += 1
        self.assertEqual(checked, 268)

    def test_basic_classical_identities(self):
        check_rewrite('p1 p2 wim', 'p2 wn p1 wn wim')
        check_rewrite('p1 wn wn', 'p1')
        check_rewrite('p1 p2 wa', 'p2 p1 wa')
        check_rewrite('p1 p2 wex', 'p1 p2 wn wal wn')

    def test_changed_boolean_function_is_rejected(self):
        for changed in ('p1 p2 wa', 'p2 p1 wim', 'p1'):
            with self.subTest(changed=changed), self.assertRaises(ValueError):
                check_rewrite('p1 p2 wim', changed)

    def test_changed_atom_or_binding_is_rejected(self):
        pairs = [('p1 p2 weq', 'p1 p2 wel'),
                 ('p1 p2 wel', 'p2 p1 wel'),
                 ('p1 p2 wal', 'p3 p2 wal'),
                 ('p1 p2 wal', 'p1 p2 wex')]
        for source, changed in pairs:
            with self.subTest(changed=changed), self.assertRaises(ValueError):
                check_rewrite(source, changed)

    def test_malformed_formula_and_configuration_are_rejected(self):
        for source in ('', 'p1 p2', 'wn', 'p1 wim', 'p4', 'p1 xyz'):
            with self.subTest(source=source), self.assertRaises(ValueError):
                parse(source)
        for choices in ({'B1': 0}, {'ICS': 256}, {'UNI': -1},
                        {'POW': True}, [], {'ICS': '0'}):
            with self.subTest(choices=choices), self.assertRaises(ValueError):
                validate_choices(choices)

    def test_factoring_audit_uses_rewritten_source(self):
        record = json.loads((ROOT / 'candidates/ics-best.json').read_text())
        self.assertIn('formula_choices', record)
        self.assertTrue(grammar_check(record)['distinguishes_return_and_halt'])
        original = build_joint(decode(record), sharing=True, compile_machine=False)
        rewritten = build_joint(decode(record), sharing=True, compile_machine=False,
                                formula_choices=record['formula_choices'])
        a = compile_fragment(original, original.main(), terminal='return')
        b = compile_fragment(rewritten, rewritten.main(), terminal='return')
        with self.assertRaises(ValueError):
            equivalent_cfg(a, b)


if __name__ == '__main__':
    unittest.main()
