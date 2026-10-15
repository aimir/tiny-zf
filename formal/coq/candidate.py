"""Prove a replacement table implements the pinned Mira program and ZF/ZFC search.

The candidate may change its control states and run time.  It must reach the
exact upstream initial tape and retain the named register-operation anchors.
Coq then checks the entire interpreter-to-set-theory proof with the new table.
This tool does not claim that a smaller table has been found.
"""
import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time


# Box.v and SymExec.v name these states in register-operation proofs.  This is
# an identity constraint, not a frozen-transition set: every candidate rebuilds
# Box.v.  Dispatcher-only states need not survive or retain their numbers.
ANCHORS = frozenset({0, 1, 2, 3, 4, 6, 28, 31, 38, 40, 43, 44, 48, 56,
                     59, 60, 63, 64, 69, 73, 75, 83, 85, 95, 96, 97, 109,
                     112, 131})
BOOT_REGS = (0, 0, 0, 0, 0, 0, 2, 0, 0) + (0,) * 136


def load_module(path, name):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def parse_table(text, halt="254"):
    """Read a deterministic two-symbol table with exactly one named terminal."""
    rows, start, fill_seen = {}, None, False
    for number, raw in enumerate(text.splitlines(), 1):
        line = raw.strip()
        if line.startswith("#!"):
            directive = line[2:].split()
            if directive and directive[0] == "start":
                if len(directive) != 2 or start is not None:
                    raise ValueError(f"line {number}: duplicate or invalid start")
                start = directive[1]
            elif directive == ["fill", "0"] and not fill_seen:
                fill_seen = True
            else:
                raise ValueError(f"line {number}: unsupported or duplicate initial-tape directive")
        elif line and not line.startswith("#"):
            parts = line.split()
            if len(parts) != 5:
                raise ValueError(f"line {number}: expected five fields")
            q, read, write, direction, target = parts
            if read not in ("0", "1") or write not in ("0", "1") or direction not in ("L", "R"):
                raise ValueError(f"line {number}: invalid transition")
            key = q, int(read)
            if key in rows:
                raise ValueError(f"line {number}: duplicate transition")
            rows[key] = int(write), direction, target
    states = {q for q, _ in rows}
    if start != "0" or "96" not in states or halt in states:
        raise ValueError("expected start 0, dispatch 96, and an undefined terminal")
    if set(rows) != {(q, b) for q in states for b in (0, 1)}:
        raise ValueError("every working state must have both transitions")
    if any(target not in states and target != halt for _, _, target in rows.values()):
        raise ValueError("transition has an undeclared nonterminal target")
    return rows


def boot_tape():
    """All occupied cells, relative to dispatch head; all other cells are blank."""
    occupied, cursor = {-1, 62}, 63
    for value in BOOT_REGS:
        cursor += 1
        occupied.update(range(cursor, cursor + value + 1))
        cursor += value + 1
    return frozenset(occupied)


def bootstrap(rows, limit):
    """Require the complete infinite tape, not merely the first nine registers."""
    expected, tape, state, head = boot_tape(), set(), "0", 0
    for steps in range(limit + 1):
        if state == "96" and len(tape) == len(expected):
            if frozenset(cell - head for cell in tape) == expected:
                return steps
        if steps == limit or (state, int(head in tape)) not in rows:
            break
        write, direction, state = rows[state, int(head in tape)]
        if write:
            tape.add(head)
        else:
            tape.discard(head)
        head += 1 if direction == "R" else -1
    raise ValueError(f"candidate did not reach the exact initial configuration within {limit} steps")


def canonicalize(rows, halt="254"):
    """Give Coq a dense table while preserving the proof's conservative anchors."""
    states = {q for q, _ in rows}
    missing = {str(q) for q in ANCHORS} - states
    if missing or max(ANCHORS) >= len(states):
        raise ValueError(f"candidate is missing required proof anchors: {sorted(missing)}")
    mapping = {str(q): q for q in ANCHORS}
    vacant = iter(q for q in range(len(states)) if q not in ANCHORS)
    def sort_key(q):
        return (0, int(q)) if q.isdecimal() else (1, q)
    for q in sorted(states - mapping.keys(), key=sort_key):
        mapping[q] = next(vacant)
    mapping[halt] = len(states)
    result = {(mapping[q], b): (w, d, mapping[target])
              for (q, b), (w, d, target) in rows.items()}
    return result, mapping


def table_text(rows):
    return "#! start 0\n" + "".join(
        f"{q} {b} {w} {d} {target}\n"
        for (q, b), (w, d, target) in sorted(rows.items()))


def coq_table(rows):
    values = []
    for q in range(len(rows) // 2):
        w0, d0, n0 = rows[q, 0]
        w1, d1, n1 = rows[q, 1]
        values.append(f"  ({str(bool(w0)).lower()}, {d0}, {n0}, "
                      f"{str(bool(w1)).lower()}, {d1}, {n1})")
    return ("(** Literal candidate table; terminal state has no row. *)\n"
            "From BusyCoq Require Import TM.\n"
            "From Coq Require Import Lists.List.\nImport ListNotations.\n\n"
            "Definition table254 : list (bool * dir * nat * bool * dir * nat) := [\n"
            + ";\n".join(values) + "\n].\n")


def replace_exact(path, old, new, count):
    source = path.read_text()
    if source.count(old) != count:
        raise ValueError(f"unexpected pinned source in {path}: {old!r}")
    path.write_text(source.replace(old, new))


def install_tree(directory, tree_path, output):
    """Generate proof data for a decoder tree and a checked source bisimulation.

    Both Python generators are untrusted: Coq checks program well-formedness,
    the binary-tape interpreter, and both directions of the certificate.
    The source interpreter and its set-theory proofs are unchanged.
    """
    tools = Path(__file__).resolve().parents[2] / "tools"
    sys.path.insert(0, str(tools))
    from compare_mira254 import REGISTERS, paths, recover
    from instruction_tree import Trees
    tree_bytes = tree_path.read_bytes()
    tree = Trees()
    root = tree.import_record(json.loads(tree_bytes), REGISTERS)
    new_paths = paths(tree, root)
    source, source_root, _ = recover((directory / "coq/prog/Dag254.v").read_text(), False)
    rmpath = load_module(directory / "tools/prog/rmpath.py", "candidate_rmpath")
    entries = rmpath.certificate(rmpath.tree_of_paths(new_paths),
                                rmpath.tree_of_paths(paths(source, source_root)))
    path_file = output / "paths.json"
    path_file.write_text(json.dumps(new_paths) + "\n")
    (output / "tree.json").write_bytes(tree_bytes)
    program_file = directory / "coq/tm/Prog254.v"
    subprocess.run([sys.executable, "-I", str(directory / "tools/tm/gen_prog.py"),
                    str(path_file), str(program_file)], check=True)
    def bits(path):
        return "[" + ";".join("t" if bit else "f" for bit in path) + "]"
    rows = [f"  ({bits(a)}, {bits(b)}, {0 if j is None else j}%N, {0 if k is None else k}%N)"
            for a, b, j, k in entries]
    certificate_file = directory / "coq/prog/Cert254.v"
    certificate_file.write_text(
        "(** Candidate-to-source bisimulation data; checked in Bisim254.v. *)\n"
        "From Coq Require Import Lists.List NArith.\n"
        "From M254P Require Import Bisim.\nImport ListNotations.\n"
        "Local Notation t := true.\nLocal Notation f := false.\n\n"
        "Definition cert254 : list entry := [\n" + ";\n".join(rows) + "\n].\n")
    return {program_file.resolve(), certificate_file.resolve()}, {
        "instruction_tree_sha256": hashlib.sha256(tree_bytes).hexdigest(),
        "program_instruction_sites": len(new_paths), "bisimulation_entries": len(entries)}


def adapt_skip_lemma(directory, table):
    """Remove an unused premise about the last skip state's read-one branch.

    A register excursion enters skip state 69 on a separator zero.  The skip
    induction scans ones only after moving to a strictly smaller register
    index, so its self-loop helper needs indices 0..7, not index 8.  Coq checks
    this tighter helper and every unchanged public box theorem.
    """
    if table[69, 1] == (1, "R", 69):
        return set(), []
    path = directory / "coq/tm/Box.v"
    old = ("Lemma sk_self j : j < 9 -> tmn (sk j) true = Some (true, R, sk j).\n"
           "Proof. intros H. do 9 (destruct j as [|j]; [reflexivity|]). lia. Qed.")
    new = old.replace("j < 9", "j < 8").replace("do 9", "do 8")
    replace_exact(path, old, new, 1)
    return {path.resolve()}, ["sk_self only asserts the eight intermediate skip self-loops"]


def compile_closure(checker, coqc, dirty, reuse):
    """Rebuild every dependent module, including the final assumption audit."""
    dirty = {path.resolve() for path in dirty}
    files = checker.closure(checker.ROOTS, checker.TOP)
    forbidden = [str(f) for f in (checker.HERE / "coq").rglob("*.v")
                 if re.search(r"\b(Admitted|admit|Axiom|Parameter)\b",
                              checker.strip_comments(f.read_text()))]
    if forbidden:
        raise ValueError(f"forbidden proof escape in {forbidden}")
    qflags = [x for prefix, dirs in checker.ROOTS.items()
              for directory in dirs for x in ("-Q", str(directory), prefix)]
    built, top_output = [], None
    for source in files:
        # All paths are resolved by the loaded checker, including on macOS where
        # /tmp and /private/tmp can otherwise silently disagree in this set.
        source = source.resolve()
        depends = {p.resolve() for p in checker.deps(checker.ROOTS, source)}
        needs_build = (not reuse or source in dirty or bool(depends & dirty)
                       or not source.with_suffix(".vo").exists())
        if not needs_build:
            continue
        dirty.add(source)
        command = [coqc, *qflags, *checker.WARN,
                   *(checker.LIBFLAGS if checker.UNDEC in source.parents else []), str(source)]
        started = time.monotonic()
        result = subprocess.run(command, cwd=checker.HERE, capture_output=True, text=True)
        if result.returncode:
            raise RuntimeError(f"Coq failed on {source}\n{result.stdout}{result.stderr}")
        built.append(source)
        print(f"{time.monotonic() - started:7.1f}s  {source.relative_to(checker.ZF)}", flush=True)
        if source == checker.TOP.resolve():
            top_output = result.stdout
            print(top_output, end="", flush=True)
    if checker.TOP.resolve() not in built or top_output is None:
        raise ValueError("the candidate end-to-end theorem was not rebuilt")
    if top_output.splitlines().count("Closed under the global context") != 3 or "Axioms:" in top_output:
        raise ValueError("candidate end-to-end assumptions audit failed")
    return len(built)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--upstream", type=Path, required=True)
    parser.add_argument("--table", type=Path, required=True)
    parser.add_argument("--tree", type=Path,
                        help="optional decoder tree JSON; also proves equivalence to the pinned source")
    parser.add_argument("--halt", default="254")
    parser.add_argument("--coqc", default=os.environ.get("COQC", "coqc"))
    parser.add_argument("--bootstrap-limit", type=int, default=2_000_000)
    parser.add_argument("--output", type=Path, required=True,
                        help="new persistent proof workspace (must not exist)")
    parser.add_argument("--reuse-upstream-build", action="store_true",
                        help="reuse existing upstream Coq objects; otherwise rebuild every source")
    args = parser.parse_args()
    coqc = shutil.which(args.coqc)
    if coqc is None:
        raise ValueError(f"Coq compiler not found: {args.coqc}")
    coqc = str(Path(coqc).absolute())
    reference = load_module(Path(__file__).with_name("check.py"), "mira_reference_check")
    upstream = args.upstream.resolve()
    _, version = reference.inspect(upstream, coqc)
    input_bytes = args.table.read_bytes()
    rows = parse_table(input_bytes.decode(), args.halt)
    steps = bootstrap(rows, args.bootstrap_limit)
    canonical, mapping = canonicalize(rows, args.halt)
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    ignore = (shutil.ignore_patterns("__pycache__") if args.reuse_upstream_build else
              shutil.ignore_patterns("*.vo", "*.vos", "*.vok", "*.glob", ".*.aux", "__pycache__"))
    for package in ("m254", "stdzf", "stdzf_r3"):
        shutil.copytree(upstream / "ZF" / package, output / "ZF" / package, ignore=ignore)
    directory = output / "ZF/m254"
    table_path = directory / "coq/tm/Table254.v"
    table_path.write_text(coq_table(canonical))
    tm_path = directory / "coq/tm/TM254.v"
    replace_exact(tm_path, "Definition NH := 254.", f"Definition NH := {len(rows) // 2}.", 1)
    boot_path = directory / "coq/tm/Boot.v"
    replace_exact(boot_path, "264982", str(steps), 2)
    replace_exact(boot_path, "264,982", f"{steps:,}", 1)
    canonical_bytes = table_text(canonical).encode()
    (output / "candidate.tm").write_bytes(canonical_bytes)
    (output / "state-map.json").write_text(json.dumps(mapping, indent=2, sort_keys=True) + "\n")
    dirty = {p.resolve() for p in (table_path, tm_path, boot_path)}
    tree_report = {}
    if args.tree:
        tree_dirty, tree_report = install_tree(directory, args.tree, output)
        dirty.update(tree_dirty)
    box_dirty, proof_adjustments = adapt_skip_lemma(directory, canonical)
    dirty.update(box_dirty)
    checker = load_module(directory / "check.py", "candidate_upstream_check")
    rebuilt = compile_closure(checker, coqc, dirty, args.reuse_upstream_build)
    report = {
        "upstream_commit": reference.COMMIT,
        "input_machine_sha256": hashlib.sha256(input_bytes).hexdigest(),
        "canonical_machine_sha256": hashlib.sha256(canonical_bytes).hexdigest(),
        "working_states": len(rows) // 2, "prover": version,
        "bootstrap_steps": steps, "exact_initial_tape": True,
        "preserved_state_anchors": sorted(ANCHORS),
        "clean_source_rebuild": not args.reuse_upstream_build,
        "proof_adjustments": proof_adjustments,
        "reused_upstream_objects": args.reuse_upstream_build, "rebuilt_modules": rebuilt,
        "theorems": reference.THEOREMS, "closed_under_global_context": 3,
        "check_pass": True, "scope": "candidate table implements the unchanged pinned source interpreter",
        **tree_report
    }
    (output / "verification.json").write_text(json.dumps(report, indent=2) + "\n")
    print(f"CANDIDATE PROOF PASS: {len(rows) // 2} states, {rebuilt} rebuilt modules", flush=True)
    return report


if __name__ == "__main__":
    main()
