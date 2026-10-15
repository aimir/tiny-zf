"""Rebuild the pinned external 254-state theorem with Coq, independently of Lean.

This checks Mira-Cult's machine and Ketchersid's proof. It does not assert that
the 308-state Lean machine has the same calculus, nor certify a search result.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys

COMMIT = "297ab8df7e5de329605c3875b4934643b371a5e3"
TABLE_HASH = "d655ce2cf8cccebd21caa21a49f0f9f010960a44b95c17aae6cc425c518954eb"
THEOREMS = ["zf254_halts_iff_ZF", "zf254_halts_iff_ZFC", "zf254_halts_iff_SIR"]


def inspect(checkout, coqc):
    def git(*args):
        return subprocess.check_output(["git", "-C", str(checkout), *args], text=True).strip()
    if git("rev-parse", "HEAD") != COMMIT:
        raise ValueError("upstream checkout is not the pinned commit")
    if git("diff", "HEAD", "--", "ZF/m254", "ZF/stdzf", "ZF/stdzf_r3"):
        raise ValueError("upstream proof sources have local changes")
    directory = checkout / "ZF/m254"
    if hashlib.sha256((directory / "machine/zfc_254.tm").read_bytes()).hexdigest() != TABLE_HASH:
        raise ValueError("upstream machine hash mismatch")
    version = subprocess.check_output([coqc, "--version"], text=True).strip()
    if "version 8.20." not in version:
        raise ValueError("this pinned proof requires Coq 8.20.x")
    return directory, version


def accept(returncode, output):
    """Require success from both the process and the upstream theorem audit."""
    lines = output.splitlines()
    return (returncode == 0 and lines.count("Closed under the global context") == 3
            and "E2E254: 3/3 closed" in lines and lines[-1:] == ["CHECK PASS"]
            and "Axioms:" not in output and "CHECK FAIL" not in output)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--upstream", type=Path, required=True)
    parser.add_argument("--coqc", default=os.environ.get("COQC", "coqc"))
    parser.add_argument("--record", type=Path)
    args = parser.parse_args()
    directory, version = inspect(args.upstream.resolve(), args.coqc)
    env = dict(os.environ, COQC=args.coqc)
    process = subprocess.Popen([sys.executable, "check.py"], cwd=directory, env=env,
                               stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    output = []
    for line in process.stdout:
        print(line, end="", flush=True)
        output.append(line)
    if not accept(process.wait(), "".join(output)):
        raise SystemExit("External Coq acceptance failed; no verification record written.")
    report = {"upstream_commit": COMMIT, "machine_sha256": TABLE_HASH,
              "working_states": 254, "prover": version,
              "clean_source_rebuild": True, "theorems": THEOREMS,
              "closed_under_global_context": 3, "check_pass": True,
              "scope": "Mira-Cult's upstream machine; not a new reduction or a Lean theorem"}
    if args.record:
        args.record.parent.mkdir(parents=True, exist_ok=True)
        args.record.write_text(json.dumps(report, indent=2) + "\n")
    return report


if __name__ == "__main__":
    main()
