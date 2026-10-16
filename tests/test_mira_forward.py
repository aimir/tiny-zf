"""Exact artifact reproduction and finite bootstrap for the proved machine."""
import hashlib
import json
import os
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'tools'))
from mira_forward import acceptance_module, build


class ForwardMachine(unittest.TestCase):
    def test_protected_startup_artifact_and_complete_tape(self):
        acceptance = acceptance_module()
        protected = acceptance.load_module(ROOT / 'formal/coq/protected.py', 'protected_test')
        table = (ROOT / 'candidates/mira250-protected.tm').read_bytes()
        tree = (ROOT / 'candidates/mira250-protected.tree.json').read_bytes()
        record = json.loads((ROOT / 'reference/mira250-protected-coq.json').read_text())
        self.assertEqual(hashlib.sha256(table).hexdigest(), record['canonical_machine_sha256'])
        self.assertEqual(hashlib.sha256(tree).hexdigest(), record['instruction_tree_sha256'])
        rows = acceptance.parse_table(table.decode(), halt='250')
        self.assertEqual({q for q, _ in rows}, {str(q) for q in range(250)})
        self.assertEqual(acceptance.bootstrap(rows, protected.STEPS, protected.CAPACITY,
                                              protected.REGISTERS, protected.PC), protected.STEPS)
        self.assertEqual(record['closed_under_global_context'], 3)
        self.assertEqual(record['bootstrap_pc_bits'], list(protected.PC))
        self.assertEqual(record['inactive_nonzero_registers'], {'615': 1})
        for filename in ('general_initialization.v', 'stack_protection.v', 'protected_startup.v'):
            proof = (ROOT / 'formal/coq' / filename).read_bytes()
            self.assertIn(filename + ' SHA256 ' + hashlib.sha256(proof).hexdigest(),
                          record['proof_adjustments'])

    def test_public_artifact_identity_and_bootstrap(self):
        acceptance = acceptance_module()
        for size, mode, steps in ((253, 'forward', 284880), (252, 'local', 267192),
                                  (251, 'startup', 182904)):
            with self.subTest(mode=mode):
                name = f'mira{size}-{mode}'
                table = (ROOT / f'candidates/{name}.tm').read_bytes()
                tree = (ROOT / f'candidates/{name}.tree.json').read_bytes()
                record = json.loads((ROOT / f'reference/{name}-coq.json').read_text())
                self.assertEqual(hashlib.sha256(table).hexdigest(), record['canonical_machine_sha256'])
                self.assertEqual(hashlib.sha256(tree).hexdigest(), record['instruction_tree_sha256'])
                rows = acceptance.parse_table(table.decode(), halt=str(size))
                self.assertEqual({q for q, _ in rows}, {str(q) for q in range(size)})
                registers = acceptance.STARTUP_REGS if mode == 'startup' else acceptance.BOOT_REGS
                self.assertEqual(acceptance.bootstrap(rows, record['bootstrap_steps'],
                                                      gap=record.get('bootstrap_pc_capacity', 62),
                                                      registers=registers), steps)
                fragments = ['forward_decrement']
                if mode in ('local', 'startup'):
                    fragments.append('local_decrement')
                if mode == 'startup':
                    fragments.append('startup_increment')
                for fragment in fragments:
                    proof = (ROOT / f'formal/coq/{fragment}.v').read_bytes()
                    self.assertIn(fragment.replace('_', '-') + ' proof fragment SHA256 '
                                  + hashlib.sha256(proof).hexdigest(), record['proof_adjustments'])

    def test_generator_reproduces_committed_artifacts(self):
        location = os.environ.get('MIRA254_UPSTREAM')
        if not location:
            self.skipTest('set MIRA254_UPSTREAM to the pinned checkout')
        for size, mode in ((253, 'forward'), (252, 'local'), (251, 'startup'), (250, 'protected')):
            with self.subTest(mode=mode):
                table, tree = build(Path(location), mode)
                self.assertEqual(table, (ROOT / f'candidates/mira{size}-{mode}.tm').read_text())
                self.assertEqual(json.dumps(tree, indent=2) + '\n',
                                 (ROOT / f'candidates/mira{size}-{mode}.tree.json').read_text())


if __name__ == '__main__':
    unittest.main()
