"""Acceptance boundaries for replacing the formally checked binary tape machine."""
import importlib.util
from pathlib import Path
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch


spec = importlib.util.spec_from_file_location(
    "mira_candidate", Path(__file__).resolve().parents[1] / "formal/coq/candidate.py")
candidate = importlib.util.module_from_spec(spec)
spec.loader.exec_module(candidate)


def boot_writer(stray=False, gap=62, registers=candidate.BOOT_REGS, pc=()):
    """A transparent fixture writing the specified tape then moving to dispatch."""
    bits = [1] + list(pc) + [0] * (gap - len(pc)) + [1]
    for value in registers:
        bits.extend([0] + [1] * (value + 1))
    if stray:
        bits.extend([0, 0, 1])
    rows = {}
    for i, bit in enumerate(bits):
        state = "0" if i == 0 else f"write{i}"
        target = f"write{i + 1}" if i + 1 < len(bits) else f"back{i - 1}"
        for read in (0, 1):
            rows[state, read] = bit, "R" if i + 1 < len(bits) else "L", target
    for i in range(len(bits) - 2, 1, -1):
        for read in (0, 1):
            rows[f"back{i}", read] = read, "L", "96" if i == 2 else f"back{i - 1}"
    for read in (0, 1):
        rows["96", read] = read, "R", "96"
    return rows, len(bits) * 2 - 3


class CandidateAcceptance(unittest.TestCase):
    def test_strict_table_parser(self):
        valid = "#! start 0\n0 0 1 R 96\n0 1 0 L 254\n96 0 0 L 0\n96 1 1 R 96\n"
        self.assertEqual(len(candidate.parse_table(valid)), 4)
        self.assertEqual(candidate.parse_table(valid + "#! fill 0\n"), candidate.parse_table(valid))
        for broken in (valid + "0 0 0 R 0\n", valid.replace("96 1 1 R 96\n", ""),
                       valid.replace("0 L 254", "0 L unknown"),
                       valid.replace("0 L 254", "0 L halt"),
                       valid.replace("#! start 0", "#! start 96"),
                       valid + "#! fill 1\n", valid + "#! tape 1001\n",
                       valid + "#! fill 0\n#! fill 0\n"):
            with self.subTest(broken=broken), self.assertRaises(ValueError):
                candidate.parse_table(broken)

    def test_canonical_mapping_preserves_machine_and_kernel(self):
        states = [str(q) for q in candidate.ANCHORS] + [f"program{i}" for i in range(110)]
        rows = {(q, b): (b, "R" if b else "L", states[(i + b + 1) % len(states)])
                for i, q in enumerate(states) for b in (0, 1)}
        rows["0", 1] = 1, "R", "254"
        table, mapping = candidate.canonicalize(rows)
        self.assertEqual(set(q for q, _ in table), set(range(len(states))))
        self.assertEqual(mapping["254"], len(states))
        for q in candidate.ANCHORS:
            self.assertEqual(mapping[str(q)], q)
        for (q, b), (w, d, target) in rows.items():
            self.assertEqual(table[mapping[q], b], (w, d, mapping[target]))

    def test_bootstrap_checks_entire_tape_and_fuel(self):
        rows, steps = boot_writer()
        self.assertEqual(candidate.bootstrap(rows, steps), steps)
        with self.assertRaises(ValueError):
            candidate.bootstrap(rows, steps - 1)
        broken, broken_steps = boot_writer(stray=True)
        with self.assertRaises(ValueError):
            candidate.bootstrap(broken, broken_steps)

    def test_startup_requires_its_exact_third_enumerator_configuration(self):
        rows, steps = boot_writer(gap=40, registers=candidate.STARTUP_REGS)
        self.assertEqual(candidate.bootstrap(rows, steps, 40, candidate.STARTUP_REGS), steps)
        with self.assertRaises(ValueError):
            candidate.bootstrap(rows, steps)
        for registers in (candidate.STARTUP_REGS[:-1],
                          candidate.STARTUP_REGS[:6] + (2,) + candidate.STARTUP_REGS[7:]):
            with self.subTest(registers=registers), self.assertRaises(ValueError):
                candidate.bootstrap(rows, steps, 40, registers)
        broken, fuel = boot_writer(stray=True, gap=40, registers=candidate.STARTUP_REGS)
        with self.assertRaises(ValueError):
            candidate.bootstrap(broken, fuel, 40, candidate.STARTUP_REGS)

    def test_nonempty_counter_and_inactive_tail_are_checked_exactly(self):
        pc, registers = (True, False, True), (3, 0, 0, 1, 0)
        rows, steps = boot_writer(gap=6, registers=registers, pc=pc)
        self.assertEqual(candidate.bootstrap(rows, steps, 6, registers, pc), steps)
        for wrong in ((), (True, True, True), (False, False, True)):
            with self.subTest(pc=wrong), self.assertRaises(ValueError):
                candidate.bootstrap(rows, steps, 6, registers, wrong)
        with self.assertRaises(ValueError):
            candidate.bootstrap(rows, steps, 6, registers[:-2] + (0, 0), pc)
        with self.assertRaisesRegex(ValueError, "must fit"):
            candidate.boot_tape(2, registers, pc)
        with self.assertRaisesRegex(ValueError, "binary"):
            candidate.boot_tape(6, registers, (2,))

    def test_startup_rejects_larger_capacity_before_reading_inputs(self):
        with patch.object(candidate.sys, "argv", ["candidate.py", "--upstream", "missing",
                          "--table", "missing", "--output", "unused",
                          "--decrement-mode", "startup", "--min-gap", "62"]):
            with self.assertRaisesRegex(ValueError, "exceeds.*exact boot capacity"):
                candidate.main()

    def test_removed_reverse_state_requires_forward_proof_mode(self):
        states = [str(q) for q in candidate.FORWARD_ANCHORS] + [f"program{i}" for i in range(110)]
        rows = {(q, b): (b, "R", "0") for q in states for b in (0, 1)}
        with self.assertRaises(ValueError):
            candidate.canonicalize(rows)
        table, mapping = candidate.canonicalize(rows, anchors=candidate.FORWARD_ANCHORS)
        self.assertNotIn("131", mapping)
        self.assertEqual(len(table), len(rows))
        for q in candidate.FORWARD_ANCHORS:
            self.assertEqual(mapping[str(q)], q)

    def test_removed_scan_state_requires_local_carry_proof_mode(self):
        states = [str(q) for q in candidate.LOCAL_ANCHORS] + [f"program{i}" for i in range(110)]
        rows = {(q, b): (b, "R", "0") for q in states for b in (0, 1)}
        for anchors in (candidate.ANCHORS, candidate.FORWARD_ANCHORS):
            with self.subTest(anchors=anchors), self.assertRaises(ValueError):
                candidate.canonicalize(rows, anchors=anchors)
        table, mapping = candidate.canonicalize(rows, anchors=candidate.LOCAL_ANCHORS)
        self.assertNotIn("131", mapping)
        self.assertNotIn("97", mapping)
        self.assertEqual(len(table), len(rows))
        for q in candidate.LOCAL_ANCHORS:
            self.assertEqual(mapping[str(q)], q)

    def test_forward_mode_replaces_kernel_and_symbolic_contract_together(self):
        with tempfile.TemporaryDirectory() as name:
            directory = Path(name)
            tm = directory / "coq/tm"
            tm.mkdir(parents=True)
            box = tm / "Box.v"
            symbolic = tm / "SymExec.v"
            box.write_text(
                "(* prefix preserved *)\n"
                "(** ** Positive decrement: shifting the later blocks left *)\n"
                "old reverse helpers\n(** ** The four excursions *)\n"
                "other operation contracts\nLemma box_decp old_contract.\n"
                "(** No axioms: *)\nPrint Assumptions box_decp.\n")
            symbolic.write_text("Definition decp_exit (r : nat) : nat := if Nat.eqb r 0 then 63 else 48.\n")
            dirty, adjustments = candidate.install_forward_decrement(directory)
            self.assertEqual(dirty, {box.resolve(), symbolic.resolve()})
            self.assertIn("other operation contracts", box.read_text())
            self.assertIn("Print Assumptions box_decp.", box.read_text())
            self.assertNotIn("old reverse helpers", box.read_text())
            self.assertNotIn("old_contract", box.read_text())
            self.assertIn("Lemma forward_dec_block", box.read_text())
            self.assertEqual(symbolic.read_text(), "Definition decp_exit (r : nat) : nat := 48.\n")
            self.assertEqual(len(adjustments), 2)
            with self.assertRaises(ValueError):
                candidate.install_forward_decrement(directory)

    def test_local_mode_preserves_file_contract_and_replaces_only_block_proof(self):
        with tempfile.TemporaryDirectory() as name:
            directory = Path(name)
            tm = directory / "coq/tm"
            tm.mkdir(parents=True)
            box = tm / "Box.v"
            symbolic = tm / "SymExec.v"
            box.write_text(
                "(** ** Positive decrement: shifting the later blocks left *)\n"
                "old reverse helpers\n(** ** The four excursions *)\n"
                "other operation contracts\nLemma box_decp old_contract.\n"
                "(** No axioms: *)\nPrint Assumptions box_decp.\n")
            symbolic.write_text("Definition decp_exit (r : nat) : nat := if Nat.eqb r 0 then 63 else 48.\n")
            dirty, adjustments = candidate.install_local_decrement(directory)
            self.assertEqual(dirty, {box.resolve(), symbolic.resolve()})
            installed = box.read_text()
            self.assertEqual(installed.count("Lemma forward_dec_block "), 1)
            self.assertEqual(installed.count("Lemma local_dec_ones "), 1)
            self.assertIn("Lemma forward_dec rest K", installed)
            self.assertIn("Lemma box_decp ", installed)
            self.assertIn("other operation contracts", installed)
            self.assertIn("Print Assumptions box_decp.", installed)
            self.assertEqual(symbolic.read_text(), "Definition decp_exit (r : nat) : nat := 48.\n")
            self.assertEqual(len(adjustments), 4)

    def test_dirty_dependency_closure_always_rebuilds_headline(self):
        with tempfile.TemporaryDirectory() as name:
            root = Path(name).resolve()
            source_dir = root / "coq"
            source_dir.mkdir()
            base, changed, child, top = [source_dir / f"{s}.v" for s in ("Base", "Table", "Sim", "End")]
            for source in (base, changed, child, top):
                source.write_text("(* fixture *)\n")
                source.with_suffix(".vo").touch()
            edges = {base: [], changed: [], child: [base, changed], top: [child]}
            checker = SimpleNamespace(
                HERE=root, ZF=root, TOP=top, UNDEC=root / "unused", ROOTS={}, WARN=[], LIBFLAGS=[],
                closure=lambda roots, top: [base, changed, child, top],
                deps=lambda roots, source: edges[source], strip_comments=lambda text: "")
            success = SimpleNamespace(returncode=0, stdout="Closed under the global context\n" * 3, stderr="")
            with patch.object(candidate.subprocess, "run", return_value=success) as compiler:
                alias = source_dir / ".." / "coq" / "Table.v"
                self.assertEqual(candidate.compile_closure(checker, "coqc", {alias}, True), 3)
                self.assertEqual([Path(c.args[0][-1]).name for c in compiler.call_args_list],
                                 ["Table.v", "Sim.v", "End.v"])
            with patch.object(candidate.subprocess, "run", return_value=success), self.assertRaises(ValueError):
                candidate.compile_closure(checker, "coqc", set(), True)

    def test_minimum_capacity_cannot_exceed_exact_boot(self):
        with tempfile.TemporaryDirectory() as name:
            directory = Path(name)
            site = directory / "coq/tm/Site.v"
            site.parent.mkdir(parents=True)
            site.write_text("Definition D0 := 40.\n")
            self.assertEqual(candidate.install_min_gap(directory, 40), (set(), []))
            for unsupported in (0, 34, 41, 63):
                with self.subTest(minimum=unsupported), self.assertRaises(ValueError):
                    candidate.install_min_gap(directory, unsupported)
            dirty, adjustments = candidate.install_min_gap(directory, 62)
            self.assertEqual(dirty, {site.resolve()})
            self.assertEqual(site.read_text(), "Definition D0 := 62.\n")
            self.assertEqual(len(adjustments), 1)
            # Fail on unexpected input instead of silently accepting a stale
            # proof workspace whose dependency objects may describe D0=40.
            with self.assertRaises(ValueError):
                candidate.install_min_gap(directory, 62)


if __name__ == "__main__":
    unittest.main()
