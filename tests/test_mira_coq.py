"""Reject incomplete or unsuccessful external proof audits."""
import importlib.util
from pathlib import Path
import unittest

spec = importlib.util.spec_from_file_location(
    "mira_coq_check", Path(__file__).resolve().parents[1] / "formal/coq/check.py")
checker = importlib.util.module_from_spec(spec)
spec.loader.exec_module(checker)


class CoqAcceptance(unittest.TestCase):
    def test_exact_success(self):
        output = "Closed under the global context\n" * 3 + "E2E254: 3/3 closed\nCHECK PASS\n"
        self.assertTrue(checker.accept(0, output))
        self.assertFalse(checker.accept(1, output))
        self.assertFalse(checker.accept(0, output.replace("3/3", "2/3")))
        self.assertFalse(checker.accept(0, output.replace("CHECK PASS", "CHECK FAIL")))
        self.assertFalse(checker.accept(0, "Axioms:\n" + output))
        self.assertFalse(checker.accept(0, output + "later error\n"))
        self.assertFalse(checker.accept(0, ""))


if __name__ == "__main__":
    unittest.main()
