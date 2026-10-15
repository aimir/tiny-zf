"""Prove a replacement table implements the pinned Mira program and ZF/ZFC search.

The candidate may change its control states and run time.  It must reach the
exact initial tape specified by its proof mode and retain the named register-operation anchors.
Coq then checks the entire interpreter-to-set-theory proof with the new table.
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
FORWARD_ANCHORS = ANCHORS - {131}
LOCAL_ANCHORS = FORWARD_ANCHORS - {97}
STARTUP_ANCHORS = LOCAL_ANCHORS
BOOT_REGS = (0, 0, 0, 0, 0, 0, 2, 0, 0) + (0,) * 136
STARTUP_REGS = (0, 1, 0, 0, 0, 0, 3, 0, 0) + (0,) * 95


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


def boot_tape(gap=62, registers=BOOT_REGS):
    """All occupied cells, relative to dispatch head; all other cells are blank."""
    occupied, cursor = {-1, gap}, gap + 1
    for value in registers:
        cursor += 1
        occupied.update(range(cursor, cursor + value + 1))
        cursor += value + 1
    return frozenset(occupied)


def bootstrap(rows, limit, gap=62, registers=BOOT_REGS):
    """Require the complete infinite tape, not merely the first nine registers."""
    expected, tape, state, head = boot_tape(gap, registers), set(), "0", 0
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


def canonicalize(rows, halt="254", anchors=ANCHORS):
    """Give Coq a dense table while preserving the proof's conservative anchors."""
    states = {q for q, _ in rows}
    missing = {str(q) for q in anchors} - states
    if missing or max(anchors) >= len(states):
        raise ValueError(f"candidate is missing required proof anchors: {sorted(missing)}")
    mapping = {str(q): q for q in anchors}
    vacant = iter(q for q in range(len(states)) if q not in anchors)
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


def install_min_gap(directory, minimum):
    """Use a PC-capacity lower bound established by the exact blank-tape boot.

    The caller rejects a requested capacity exceeding the exact boot tape's
    capacity. The Sim invariant then preserves it, without a new premise in
    the headline theorem. Every dependent proof is rebuilt below.
    """
    if minimum not in (40, 62):
        raise ValueError("minimum PC capacity must be 40 or 62")
    if minimum == 40:
        return set(), []
    path = directory / "coq/tm/Site.v"
    replace_exact(path, "Definition D0 := 40.", "Definition D0 := 62.", 1)
    return {path.resolve()}, ["minimum PC capacity strengthened from 40 to the exact boot capacity 62"]


def install_forward_decrement(directory):
    """Prove the streaming decrement kernel with a uniform return state 48.

    The forward and local modes drop state 131 from the canonicalization anchors.
    Its replacement proof handles unbounded register values and arbitrary
    left context; all literal transitions and subsequent sites are checked by
    Coq. The source interpreter and the exact initial tape remain unchanged.
    """
    fragment = Path(__file__).with_name("forward_decrement.v").read_text()
    helpers, separator, contract = fragment.partition("Lemma box_decp ")
    if not separator or "Lemma box_decp " in contract:
        raise ValueError("invalid forward-decrement proof fragments")
    path = directory / "coq/tm/Box.v"
    source = path.read_text()
    start = "(** ** Positive decrement: shifting the later blocks left *)"
    end = "(** ** The four excursions *)"
    if source.count(start) != 1 or source.count(end) != 1:
        raise ValueError("unexpected pinned positive-decrement helper section")
    before, rest = source.split(start)
    _, after = rest.split(end)
    source = before + helpers + "\n" + end + after
    if source.count("Lemma box_decp ") != 1 or source.count("(** No axioms: *)") != 1:
        raise ValueError("unexpected pinned positive-decrement contract")
    before, rest = source.split("Lemma box_decp ")
    _, after = rest.split("(** No axioms: *)")
    path.write_text(before + separator + contract + "\n(** No axioms: *)" + after)
    symbolic = directory / "coq/tm/SymExec.v"
    replace_exact(symbolic,
                  "Definition decp_exit (r : nat) : nat := if Nat.eqb r 0 then 63 else 48.",
                  "Definition decp_exit (r : nat) : nat := 48.", 1)
    return {path.resolve(), symbolic.resolve()}, [
        "positive decrement streams the gap rightward and returns in state 48 for every register",
        "forward-decrement proof fragment SHA256 " + hashlib.sha256(fragment.encode()).hexdigest()]


def install_local_decrement(directory):
    """Replace the forward block scan with a local erased-cell carry.

    The block contract is identical: the carry moves right through each
    register without changing its value. This permits removing state 97;
    all remaining unbounded file and operation proofs are reused and rebuilt.
    """
    dirty, adjustments = install_forward_decrement(directory)
    fragment = Path(__file__).with_name("local_decrement.v").read_text()
    path = directory / "coq/tm/Box.v"
    source = path.read_text()
    marker = "Lemma forward_dec_block "
    if source.count(marker) != 1:
        raise ValueError("unexpected forward-decrement block proof")
    start = source.index(marker)
    end = source.index("Qed.", start) + len("Qed.")
    path.write_text(source[:start] + fragment.rstrip() + source[end:])
    adjustments.extend([
        "positive decrement carries an erased cell by local swaps, eliminating state 97",
        "local-decrement proof fragment SHA256 " + hashlib.sha256(fragment.encode()).hexdigest()])
    return dirty, adjustments


def install_startup(directory):
    """Prove the shared startup and its exact third enumerator state.

    The increment detour and uniform mark exit are checked for unbounded
    register files. The frozen abstract enumerator is unchanged: a computed
    nonhalting step connects its old initial state s2 to the new state s3.
    """
    dirty, adjustments = install_local_decrement(directory)
    tm = directory / "coq/tm"
    fragment = Path(__file__).with_name("startup_increment.v").read_text()
    path = tm / "Box.v"
    source = path.read_text()
    if source.count("Lemma shift_inc ") != 1:
        raise ValueError("unexpected increment proof")
    start = source.index("Lemma shift_inc ")
    end = source.index("Qed.", start) + len("Qed.")
    path.write_text(source[:start] + fragment.rstrip() + source[end:])
    replace_exact(tm / "SymExec.v",
                  "Definition mark_exit (r : nat) : nat := if Nat.eqb r 0 then 2 else 6.",
                  "Definition mark_exit (r : nat) : nat := 6.", 1)
    replace_exact(tm / "Prog254.v", "Definition R0 : regs := upd regs0 0 2.",
                  "Definition R0 : regs := upd (upd regs0 0 3) 4 1.", 1)
    replace_exact(tm / "Boot.v", "[0; 0; 0; 0; 0; 0; 2; 0; 0] ++ repeat 0 136",
                  "[0; 1; 0; 0; 0; 0; 3; 0; 0] ++ repeat 0 95", 1)
    replace_exact(tm / "Boot.v", "zeros 62 ++ true :: sepsR boot_regs",
                  "zeros 40 ++ true :: sepsR boot_regs", 1)
    replace_exact(tm / "Boot.v", "62 zero cells, the header 1, then 145 register blocks",
                  "40 zero cells, the header 1, then 104 register blocks", 1)
    replace_exact(tm / "Boot.v", "136 extra) with values 0,0,0,0,0,0,2,0,0 and 136 zeros.",
                  "95 extra) with values 0,1,0,0,0,0,3,0,0 and 95 zeros.", 1)
    replace_exact(tm / "Sim.v", "exists (@nil bool), R0, 62, (repeat 0 136).",
                  "exists (@nil bool), R0, 40, (repeat 0 95).", 1)
    main = directory / "coq/prog/Main254.v"
    replace_exact(main, "Definition s2 : state := mkState 0 2 0 0 0 0.",
                  "Definition s2 : state := mkState 0 2 0 0 0 0.\n"
                  "Definition s3 : state := mkState 0 3 0 0 1 0.", 1)
    replace_exact(main, "Lemma R0_enc : approx R0 (enc s2).",
                  "Lemma R0_enc : approx R0 (enc s3).", 1)
    bridge = """(** The third enumerator step is nonhalting and reaches exactly the
    startup register values. The equivalence preserves both halting directions. *)
Lemma s2_step3 : enum_step s2 = Some s3.
Proof. vm_compute. reflexivity. Qed.

Lemma enum_s3 : enum254_halts <-> halts_from s3.
Proof. rewrite enum_s2. apply halts_from_step, s2_step3. Qed.

"""
    replace_exact(main, "Theorem prog254 :", bridge + "Theorem prog254 :", 1)
    replace_exact(main, "iter_halts_dag s2 R0 R0_enc", "iter_halts_dag s3 R0 R0_enc", 1)
    replace_exact(main, "symmetry. exact enum_s2.", "symmetry. exact enum_s3.", 1)
    replace_exact(main, "R0 = nextproof 2, all other registers 0",
                  "R0 = nextproof 3, param1 1, all other registers 0", 1)
    replace_exact(main, "the boot state R0 encodes s2, which s0 reaches in two steps.",
                  "the boot state R0 encodes s3, which s0 reaches in three steps.", 1)
    dirty.update(p.resolve() for p in (tm / "Prog254.v", tm / "Boot.v", tm / "Sim.v", main))
    adjustments.extend([
        "mark returns uniformly in state 6; increment returns through the shared scanner",
        "startup-increment proof fragment SHA256 " + hashlib.sha256(fragment.encode()).hexdigest(),
        "exact initial registers encode s3, proved to follow s2 by one nonhalting enumerator step"])
    return dirty, adjustments


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
    parser.add_argument("--decrement-mode", choices=("reverse", "forward", "local", "startup"), default="reverse",
                        help="kernel proof: reverse, forward, local carry, or local carry with shared startup")
    parser.add_argument("--coqc", default=os.environ.get("COQC", "coqc"))
    parser.add_argument("--bootstrap-limit", type=int, default=2_000_000)
    parser.add_argument("--min-gap", type=int, choices=(40, 62),
                        help="minimum PC capacity (default: exact boot capacity, 40 in startup mode, else 62)")
    parser.add_argument("--output", type=Path, required=True,
                        help="new persistent proof workspace (must not exist)")
    parser.add_argument("--reuse-upstream-build", action="store_true",
                        help="reuse existing upstream Coq objects; otherwise rebuild every source")
    args = parser.parse_args()
    boot_gap, boot_registers = ((40, STARTUP_REGS) if args.decrement_mode == "startup"
                                else (62, BOOT_REGS))
    if args.min_gap is None:
        args.min_gap = boot_gap
    if args.min_gap > boot_gap:
        raise ValueError("minimum PC capacity exceeds the proof mode's exact boot capacity")
    coqc = shutil.which(args.coqc)
    if coqc is None:
        raise ValueError(f"Coq compiler not found: {args.coqc}")
    coqc = str(Path(coqc).absolute())
    reference = load_module(Path(__file__).with_name("check.py"), "mira_reference_check")
    upstream = args.upstream.resolve()
    _, version = reference.inspect(upstream, coqc)
    input_bytes = args.table.read_bytes()
    rows = parse_table(input_bytes.decode(), args.halt)
    steps = bootstrap(rows, args.bootstrap_limit, boot_gap, boot_registers)
    anchors = {"reverse": ANCHORS, "forward": FORWARD_ANCHORS,
               "local": LOCAL_ANCHORS, "startup": STARTUP_ANCHORS}[args.decrement_mode]
    canonical, mapping = canonicalize(rows, args.halt, anchors)
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
    if args.decrement_mode in ("forward", "local", "startup"):
        installer = {"forward": install_forward_decrement, "local": install_local_decrement,
                     "startup": install_startup}[args.decrement_mode]
        forward_dirty, forward_adjustments = installer(directory)
        dirty.update(forward_dirty)
        proof_adjustments.extend(forward_adjustments)
    gap_dirty, gap_adjustments = install_min_gap(directory, args.min_gap)
    dirty.update(gap_dirty)
    proof_adjustments.extend(gap_adjustments)
    checker = load_module(directory / "check.py", "candidate_upstream_check")
    rebuilt = compile_closure(checker, coqc, dirty, args.reuse_upstream_build)
    report = {
        "upstream_commit": reference.COMMIT,
        "input_machine_sha256": hashlib.sha256(input_bytes).hexdigest(),
        "canonical_machine_sha256": hashlib.sha256(canonical_bytes).hexdigest(),
        "working_states": len(rows) // 2, "prover": version,
        "bootstrap_steps": steps, "exact_initial_tape": True,
        "bootstrap_pc_capacity": boot_gap,
        "initial_enumerator_steps": 3 if args.decrement_mode == "startup" else 2,
        "minimum_pc_capacity": args.min_gap,
        "preserved_state_anchors": sorted(anchors),
        "positive_decrement_implementation": args.decrement_mode,
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
