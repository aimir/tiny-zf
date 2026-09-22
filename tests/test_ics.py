"""Checks at the boundaries of the experimental ICS source transformations."""
from pathlib import Path
import sys
import unittest

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'tools'))
from ics import ICS,validate_ics_order
from joint import PermutedICS
from verify import fingerprints
from verify_ics import arithmetic_checks,source_checks
from encoding import ReversedFusion
from register_check import compile_fragment,execute


class ICSTests(unittest.TestCase):
    def test_port_matches_pinned_formulas(self):
        result=source_checks()
        self.assertEqual(result['published_constructor_sequences'],5)
        self.assertEqual(result['schema_renaming_cases'],90)

    def test_identity_parameter_permutation_preserves_source(self):
        self.assertEqual(fingerprints(ICS()),fingerprints(PermutedICS()))

    def test_guard_phase_cannot_be_moved_early(self):
        order=list(range(17));order[0],order[12]=order[12],order[0]
        with self.assertRaisesRegex(ValueError,'safety phases'):
            validate_ics_order(order)

    def test_axiom_cannot_be_deleted(self):
        with self.assertRaisesRegex(ValueError,'invalid ICS order'):
            validate_ics_order(list(range(16)))

    def test_storage_and_constructor_differentials(self):
        result=arithmetic_checks()
        self.assertEqual(result,{'guard_cases':500,'detachment_cases':48,'constructor_cases':1440})

    def test_distinguished_codes_survive_recoding(self):
        for op,wanted in [('weq',0),('wel',1)]:
            machine=ReversedFusion();machine.tag_mode=1;machine.binary_mode=0
            registers,_=execute(compile_fragment(machine,getattr(machine,op)()))
            self.assertEqual(registers.get('topwff',0),wanted)
            self.assertEqual(registers.get('wffstack',0),0)


if __name__=='__main__':
    unittest.main()
