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
    def test_public_artifact_identity_and_bootstrap(self):
        acceptance = acceptance_module()
        table = (ROOT / 'candidates/mira253-forward.tm').read_bytes()
        tree = (ROOT / 'candidates/mira253-forward.tree.json').read_bytes()
        record = json.loads((ROOT / 'reference/mira253-forward-coq.json').read_text())
        self.assertEqual(hashlib.sha256(table).hexdigest(), record['canonical_machine_sha256'])
        self.assertEqual(hashlib.sha256(tree).hexdigest(), record['instruction_tree_sha256'])
        rows = acceptance.parse_table(table.decode(), halt='253')
        self.assertEqual({q for q, _ in rows}, {str(q) for q in range(253)})
        self.assertEqual(acceptance.bootstrap(rows, record['bootstrap_steps']), 284880)
        proof = (ROOT / 'formal/coq/forward_decrement.v').read_bytes()
        self.assertIn('forward-decrement proof fragment SHA256 ' + hashlib.sha256(proof).hexdigest(),
                      record['proof_adjustments'])

    def test_generator_reproduces_both_committed_artifacts(self):
        location = os.environ.get('MIRA254_UPSTREAM')
        if not location:
            self.skipTest('set MIRA254_UPSTREAM to the pinned checkout')
        table, tree = build(Path(location))
        self.assertEqual(table, (ROOT / 'candidates/mira253-forward.tm').read_text())
        self.assertEqual(json.dumps(tree, indent=2) + '\n',
                         (ROOT / 'candidates/mira253-forward.tree.json').read_text())


if __name__ == '__main__':
    unittest.main()
