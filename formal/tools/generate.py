#!/usr/bin/env python3
"""Import the literal candidate and source schemas; Lean checks the proofs.

--check independently rebuilds these imports and compares every byte. No logs,
search history or execution samples enter the generated definitions.
"""
from pathlib import Path
import argparse
import json
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'tools'))
from machines import read_table
from ics import RPN, LOGICAL, PROTECTED
from joint import LOGIC_RPN, PERMUTATIONS
from formula_rewrite import rewrite


def expression(rpn, permutation):
    stack = []
    for token in rpn.split():
        if token.startswith('p'):
            stack.append('p' + str(permutation[int(token[1:]) - 1]))
        elif token == 'wn':
            stack.append(f'(wn {stack.pop()})')
        else:
            b, a = stack.pop(), stack.pop()
            stack.append(f'({token} {a} {b})')
    assert len(stack) == 1
    return stack[0]


def sources():
    record = json.loads((ROOT / 'candidates/ics-best.json').read_text())
    assert record['reverse_payload'] and record['final_states'] == 308
    assert record['decoder']['order'] == ['param1', 'param3', 'param2', 'axiomcode']
    start, edges = read_table(ROOT / 'candidates/ics-best.tm')
    names = sorted({q for q, _ in edges})
    assert len(names) == 308 and start == names[0]
    index = {q: i for i, q in enumerate(names)}
    machine = ['import TinyZF.Machine', '', 'set_option maxRecDepth 8192', '', '/-! Literal import of candidates/ics-best.tm. Regenerate with formal/tools/generate.py. -/',
               'namespace TinyZF.Machine308', '', '/-- Original labels, in the numeric state order. -/',
               'def labels : Vector String 308 := ⟨#[']
    machine += ['  ' + json.dumps(q) + ',' for q in names]
    machine += ['], by decide⟩', '', '/-- Two transitions per working state, in read-bit order 0,1.',
                'An absent transition and an explicit halt remain distinct. -/',
                'def table : Vector (Option (Transition 308)) 616 := ⟨#[']
    for q in names:
        for bit in '01':
            edge = edges.get((q, bit))
            if edge is None:
                row = 'none'
            else:
                w, d, target = edge
                t = 'none' if target == 'halt' else f'some {index[target]}'
                row = f'some ⟨{str(w == "1").lower()}, {str(d == "R").lower()}, {t}⟩'
            machine.append(f'  {row}, -- {q} / {bit}')
    machine += ['], by decide⟩', '', '/-- The literal machine, with no extra working states. -/',
                'def machine : Machine 308 := fun q b => table.get ⟨2 * q.val + (if b then 1 else 0), by cases b <;> simp <;> omega⟩',
                '', '/-- Blank tape, head at zero, original initial label `0.boot.A`. -/',
                'def initial : Configuration 308 := ⟨some 0, 0, fun _ => false⟩',
                '', '/-- The intended binary-tape halting proposition. -/',
                'def Halts : Prop := Machine.halts machine initial',
                '', '/-- The state type has exactly 308 working states; halting is separate. -/',
                'theorem state_count : Fintype.card (Fin 308) = 308 := by simp',
                '', 'end TinyZF.Machine308', '']
    schema = ['import TinyZF.Cantor', '', '/-! The 15 axiom-producing clauses, in logical then protected order.',
              'Imported from the current candidate settings, including reversed binary payloads,',
              'per-schema parameter permutations, protected safety guards and selected rewrites. -/',
              'namespace TinyZF.Source', 'open Cantor', '',
              '/-- Equality constructor in the reversed payload convention. -/', 'def weq (a b : Nat) := pair (pair b a) 0',
              '/-- Membership constructor. -/', 'def wel (a b : Nat) := pair (pair b a) 1',
              '/-- Implication constructor. -/', 'def wim (a b : Nat) := pair (pair b a) 2',
              '/-- Negation constructor (its payload is unary). -/', 'def wn (a : Nat) := pair a 3',
              '/-- Universal quantification constructor. -/', 'def wal (x a : Nat) := pair (pair a x) 4',
              '/-- Existential quantification expands as not-forall-not. -/', 'def wex (x a : Nat) := wn (wal x (wn a))',
              '/-- Conjunction expands as not-implication-not. -/', 'def wa (a b : Nat) := wn (wim a (wn b))',
              '/-- Avoid capture at the protected phase, exactly as the source does. -/',
              'def safe (a b : Nat) := if a = b then a + 1 else a', '',
              '/-- The current source axiom instances. Numeric parameters are unrestricted.',
              'The protected guards are part of the instance definition. -/',
              'def schema (k : Fin 15) (p1 p2 p3 : Nat) : Nat :=', '  match k.val with']
    names_axiom = list(LOGICAL[2:]) + list(PROTECTED)
    for k, name in enumerate(names_axiom):
        protected = name in PROTECTED
        perm = PERMUTATIONS[record['protected_permutation'] if protected else record['parameter_permutations'][name]]
        text = rewrite(RPN[name], record['formula_choices'][name]) if protected else LOGIC_RPN[name]
        schema += [f'  | {k if k < 14 else "_"} => -- {name}']
        if protected:
            a, b, c = [f'p{i}' for i in perm]
            schema += [f'    let {a} := safe {a} {c}', f'    let {b} := safe {b} {c}']
        schema += ['    ' + expression(text, perm)]
    selectors = [record['order'].index(k + 2) + 1 for k in range(15)]
    schema += ['', '/-- Inference clauses and schema instances are kept distinct. -/',
               'inductive Clause where',
               '  | moot | detach | generalize | axiom (k : Fin 15)',
               '  deriving DecidableEq', '',
               '/-- Actual candidate selector order; large positive selectors saturate at the last clause. -/',
               'def dispatch : Nat → Clause', '  | 0 => .moot']
    for i, clause in enumerate(record['order']):
        target = '.detach' if clause == 0 else '.generalize' if clause == 1 else f'.axiom {clause - 2}'
        schema += [f'  | {i+1 if i < 16 else "_"} => {target}']
    assert record['order'][-1] >= 2
    schema += ['', '/-- Each schema has a selectable code in the compiled clause order. -/',
               'def schemaSelector (k : Fin 15) : Nat :=',
               '  (⟨#[' + ', '.join(map(str, selectors)) + '], by decide⟩ : Vector Nat 15).get k',
               '', 'end TinyZF.Source', '']
    original = ['import TinyZF.Schemas', '', '/-! Protected schemas before Boolean rewrites, with the same guards and parameter permutation. -/',
                'namespace TinyZF.Source', '', '/-- The corrected published ICS source before the selected rewrites. -/',
                'def originalProtected (k : Fin 5) (p1 p2 p3 : Nat) : Nat :=', '  match k.val with']
    perm = PERMUTATIONS[record['protected_permutation']]
    a,b,c = [f'p{i}' for i in perm]
    for k,name in enumerate(PROTECTED):
        original += [f'  | {k if k < 4 else "_"} => -- {name}',
                     f'    let {a} := safe {a} {c}', f'    let {b} := safe {b} {c}',
                     '    ' + expression(RPN[name], perm)]
    original += ['', 'end TinyZF.Source', '']
    return {'Machine308.lean': '\n'.join(machine), 'Schemas.lean': '\n'.join(schema),
            'ProtectedOriginal.lean': '\n'.join(original)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    for name, data in sources().items():
        path = ROOT / 'formal/TinyZF' / name
        if args.check:
            if path.read_text() != data:
                raise SystemExit(f'Generated import differs: {name}')
        else:
            path.write_text(data)
    print('Literal machine and current schema imports match.' if args.check else 'Generated machine and schema imports.')


if __name__ == '__main__':
    main()
