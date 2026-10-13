#!/usr/bin/env python3
"""Check the complete tape-to-source Lean theorem, its scope, and exact candidate imports."""
from pathlib import Path
import argparse
import hashlib
import json
import os
import re
import subprocess
import sys

FORMAL = Path(__file__).resolve().parents[1]
ROOT = FORMAL.parent
sys.path.insert(0, str(ROOT / 'tools'))
from decoder import allocation_plan
from generate import sources

MACHINE_HASH = 'c4083dd0239b8f5c9bd231c69caff51bca8c5a3d0a0679e92f89bae158817d16'
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def check_imports(root=ROOT):
    if digest(root / 'candidates/ics-best.tm') != MACHINE_HASH:
        raise ValueError('The 308-state literal table changed')
    for name, expected in sources().items():
        if (root / 'formal/TinyZF' / name).read_text() != expected:
            raise ValueError(f'Generated import differs: {name}')
    record = json.loads((root / 'candidates/ics-best.json').read_text())
    actual = allocation_plan(record['decoder'])
    text = (root / 'formal/TinyZF/Decoder.lean').read_text()
    body = text.split('def plan : List Operation := [', 1)[1].split(']', 1)[0]
    lean = []
    for op in body.split(','):
        tokens = op.strip().replace('.', '').split()
        if tokens:
            tokens[0] = {'split': 'unpair'}.get(tokens[0], tokens[0])
            lean.append(tuple(tokens))
    if actual != lean:
        raise ValueError('The Lean allocation plan differs from the candidate')


def run(command):
    result = subprocess.run(command, cwd=FORMAL, text=True, capture_output=True,
        env={**os.environ, 'LEAN_NUM_THREADS': '1'})
    output = result.stdout + result.stderr
    print(output if len(output) < 6000 else output[-6000:], end='', flush=True)
    if result.returncode:
        raise SystemExit(result.returncode)
    return output


def audit_axioms(output):
    results = {}
    names = re.findall(r'^#print axioms ([\w.]+)', (FORMAL / 'Audit.lean').read_text(), re.M)
    for name in names:
        found = re.search(r"'" + re.escape(name) + r"' depends on axioms:\s*\[([^\]]*)\]", output)
        if found:
            axioms = {x.strip() for x in found[1].split(',') if x.strip()}
        elif f"'{name}' does not depend on any axioms" in output:
            axioms = set()
        else:
            raise ValueError(f'Missing axiom report: {name}')
        if not axioms <= ALLOWED:
            raise ValueError(f'Unpermitted axioms: {name}: {axioms - ALLOWED}')
        results[name] = sorted(axioms)
    return results


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--record', action='store_true', help='refresh the compact verification manifest after success')
    args = parser.parse_args()
    check_imports()
    run(['lake', 'build'])
    axioms = audit_axioms(run(['lake', 'env', 'lean', '--memory=8192', '--threads=1', 'Audit.lean']))
    files = sorted(FORMAL.glob('*.lean')) + sorted((FORMAL / 'TinyZF').rglob('*.lean'))
    files += [FORMAL / x for x in ('lean-toolchain', 'lakefile.toml', 'lake-manifest.json')]
    report = {
        'status': 'complete Lean verification of the literal tape machine against the numeric source calculus',
        'headline': 'TinyZF.machine_correct',
        'statement': 'Machine308.Halts ↔ Source.Provable 1',
        'end_to_end_machine_verification': True,
        'zf_equiconsistency_verification': False,
        'machine_sha256': MACHINE_HASH,
        'theorem_axioms': axioms,
        'source_sha256': {str(p.relative_to(FORMAL)): digest(p) for p in files},
    }
    path = FORMAL / 'verification.json'
    if args.record:
        path.write_text(json.dumps(report, indent=2) + '\n')
    elif json.loads(path.read_text()) != report:
        raise ValueError('Stale verification record; recheck and refresh with --record')
    print('ACCEPTED: complete literal tape-machine/source-calculus equivalence; conventional-ZF interpretation and independence remain outside the claim.')


if __name__ == '__main__':
    main()
