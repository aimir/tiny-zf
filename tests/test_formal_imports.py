"""Negative tests for the formalization's artifact and axiom acceptance boundary."""
from pathlib import Path
import importlib.util
import re
import shutil
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'formal/tools'))
spec = importlib.util.spec_from_file_location('tiny_zf_formal_check', ROOT / 'formal/tools/check.py')
check = importlib.util.module_from_spec(spec)
spec.loader.exec_module(check)


class FormalImports(unittest.TestCase):
    def fixture(self):
        temporary = tempfile.TemporaryDirectory(prefix='tiny-zf-formal-test-')
        self.addCleanup(temporary.cleanup)
        root = Path(temporary.name)
        shutil.copytree(ROOT / 'candidates', root / 'candidates')
        shutil.copytree(ROOT / 'formal/TinyZF', root / 'formal/TinyZF')
        return root

    def test_current_imports(self):
        check.check_imports()

    def test_rejects_changed_literal_table(self):
        root = self.fixture()
        path = root / 'candidates/ics-best.tm'
        path.write_text(path.read_text().replace('0.boot.A 0 1 R', '0.boot.A 0 0 R', 1))
        with self.assertRaisesRegex(ValueError, 'literal table changed'):
            check.check_imports(root)

    def test_rejects_changed_schema_guard(self):
        root = self.fixture()
        path = root / 'formal/TinyZF/Schemas.lean'
        path.write_text(path.read_text().replace('then a + 1 else a', 'then a else a', 1))
        with self.assertRaisesRegex(ValueError, 'Generated import differs'):
            check.check_imports(root)

    def test_rejects_changed_allocation(self):
        root = self.fixture()
        path = root / 'formal/TinyZF/Decoder.lean'
        path.write_text(path.read_text().replace('.clear .param1', '.clear .nextproof', 1))
        with self.assertRaisesRegex(ValueError, 'allocation plan differs'):
            check.check_imports(root)

    def test_rejects_unpermitted_axiom(self):
        names = re.findall(r'^#print axioms ([\w.]+)', (ROOT / 'formal/Audit.lean').read_text(), re.M)
        output = '\n'.join(f"'{name}' does not depend on any axioms" for name in names[1:])
        output += f"\n'{names[0]}' depends on axioms: [sorryAx]"
        with self.assertRaisesRegex(ValueError, 'Unpermitted axioms'):
            check.audit_axioms(output)

    def test_rejects_missing_axiom_report(self):
        with self.assertRaisesRegex(ValueError, 'Missing axiom report'):
            check.audit_axioms('')


if __name__ == '__main__':
    unittest.main()
