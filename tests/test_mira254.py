"""The external-program importer must reject malformed graphs and preserve exits."""
import sys
from pathlib import Path
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
from compare_mira254 import recover, cfg
from verify_tree import equivalent_increment_cfg


class MiraImportTests(unittest.TestCase):
    def test_two_formats_have_same_control_flow(self):
        a, ar, _ = recover('(CI 0, CH)', True)
        b, br, _ = recover('| 0 => (EInc 0, EHalt)', False)
        self.assertEqual(equivalent_increment_cfg(cfg(a, ar), cfg(b, br)), 1)

    def test_missing_child_rejected(self):
        with self.assertRaisesRegex(ValueError, 'missing or cyclic'):
            recover('(CN 1, CH)', True)

    def test_cycle_rejected(self):
        with self.assertRaisesRegex(ValueError, 'missing or cyclic'):
            recover('(CN 0, CH)', True)

    def test_unknown_register_rejected(self):
        with self.assertRaisesRegex(ValueError, 'register'):
            recover('(CI 9, CH)', True)

    def test_duplicate_node_rejected(self):
        with self.assertRaisesRegex(ValueError, 'duplicate'):
            recover('| 0 => (EInc 0, EHalt)\n| 0 => (EInc 1, EHalt)', False)

    def test_distinct_register_effect_rejected(self):
        a, ar, _ = recover('(CI 0, CH)', True)
        b, br, _ = recover('(CI 1, CH)', True)
        with self.assertRaisesRegex(ValueError, 'different increment'):
            equivalent_increment_cfg(cfg(a, ar), cfg(b, br))


if __name__ == '__main__':
    unittest.main()
