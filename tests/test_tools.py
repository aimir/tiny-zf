"""Regression checks for trust-boundary parsing and reduction certificates."""
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
from machines import DISTINCT_ORDER, UPSTREAM_ORDER, read_table, totalize, validate_order
from reduce import check_quotient, local_macro, quotient


class TableTests(unittest.TestCase):
    def parse(self, text):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'test.tm'
            path.write_text(text)
            return read_table(path)

    def test_nonblank_input_rejected(self):
        with self.assertRaisesRegex(ValueError, 'tape directive'):
            self.parse('#! start q\n#! write 1\nq 0 0 R halt\n')

    def test_duplicate_row_rejected(self):
        with self.assertRaisesRegex(ValueError, 'duplicate transition'):
            self.parse('#! start q\nq 0 0 R halt\nq 0 1 L q\n')

    def test_unexpected_missing_target_rejected(self):
        with self.assertRaisesRegex(ValueError, 'undefined target'):
            self.parse('#! start q\nq 0 0 R typo\n')

    def test_nonbinary_rejected(self):
        with self.assertRaisesRegex(ValueError, 'binary'):
            self.parse('#! start q\nq 0 2 R halt\n')

    def test_missing_read_gets_one_step_to_halt(self):
        start, edges = self.parse('#! start q\nq 0 1 L q\n')
        self.assertNotIn(('q', '1'), edges)
        self.assertEqual(totalize(start, edges)['!ENTRY'][1], (1, 1, 'HALT'))


class ReductionTests(unittest.TestCase):
    def test_exact_quotient_and_corrupt_certificate(self):
        rows = {'!ENTRY': ((0, 1, 'a'), (1, 1, 'b')),
                'a': ((1, -1, 'HALT'), (0, 1, 'a')),
                'b': ((1, -1, 'HALT'), (0, 1, 'b'))}
        out, mapping = quotient(rows)
        self.assertEqual(len(out), 2)
        self.assertEqual(mapping['a'], mapping['b'])
        corrupt = out.copy()
        corrupt[mapping['a']] = ((0, -1, 'HALT'), out[mapping['a']][1])
        with self.assertRaisesRegex(ValueError, 'transition mismatch'):
            check_quotient(rows, corrupt, mapping)

    def test_macro_preserves_other_cells(self):
        rows = {'!ENTRY': ((0, 1, 'a'), (1, 1, 'a')),
                'a': ((0, -1, 'b'), (1, -1, 'b')),
                'b': ((1, 1, 'HALT'), (1, 1, 'HALT'))}
        self.assertEqual(local_macro(rows, '!ENTRY', 0, 3), (1, 1, 'HALT'))
        rows['a'] = ((0, -1, 'b'), (0, -1, 'b'))
        self.assertIsNone(local_macro(rows, '!ENTRY', 0, 3))


class ClauseTests(unittest.TestCase):
    def test_allowed_orders(self):
        validate_order(UPSTREAM_ORDER)
        validate_order(DISTINCT_ORDER)

    def test_missing_real_axiom_rejected(self):
        with self.assertRaisesRegex(ValueError, 'missing'):
            validate_order(tuple(i for i in DISTINCT_ORDER if i != 19))

    def test_inference_clause_cannot_be_last(self):
        with self.assertRaisesRegex(ValueError, 'last'):
            validate_order(tuple(i for i in DISTINCT_ORDER if i != 0) + (0,))


if __name__ == '__main__':
    unittest.main()
