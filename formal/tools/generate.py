#!/usr/bin/env python3
"""Import the literal candidate and source schemas; Lean checks the proofs.

--check independently rebuilds these imports and compares every byte. No diagnostic logs or search history enter the generated definitions.
Finite execution checkpoints are proposed certificates checked by Lean.
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
from program_certificate import program_source
from graph_certificate import graph_sources
from placement_certificate import placement_source


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


def schema_code_source(record):
    """Import stack expressions, with their numeric agreement checked by Lean."""
    def ast(rpn, permutation):
        stack = []
        def unary(k, a): return f'(.unary {k} {a})'
        def binary(k, a, b): return f'(.binary {k} {a} {b})'
        for token in rpn.split():
            if token.startswith('p'):
                stack.append(f'(.parameter {permutation[int(token[1:])-1]-1})')
            elif token == 'wn':
                stack.append(unary(3, stack.pop()))
            else:
                b, a = stack.pop(), stack.pop()
                if token == 'wex': out = unary(3, binary(4, a, unary(3, b)))
                elif token == 'wa': out = unary(3, binary(2, a, unary(3, b)))
                else: out = binary({'weq':0, 'wel':1, 'wim':2, 'wal':4}[token], a, b)
                stack.append(out)
        assert len(stack) == 1
        return stack[0]
    lines = ['import TinyZF.Interpreter.Expressions', '',
        '/-! # The fixed schema expressions and their independent specification', '',
        'Generated expression trees describe primitive stack code. The theorem',
        'below checks their values against the existing source schema definitions;',
        'the generator is not a correctness assumption. -/',
        'namespace TinyZF.Interpreter.SchemaCode', 'open Expressions', '',
        '/-- Stack expression for each of the fifteen fixed schema clauses. -/',
        'def expression (k : Fin 15) : Expr :=', '  match k.val with']
    for k, name in enumerate(list(LOGICAL[2:])+list(PROTECTED)):
        protected = name in PROTECTED
        perm = PERMUTATIONS[record['protected_permutation'] if protected else record['parameter_permutations'][name]]
        rpn = rewrite(RPN[name], record['formula_choices'][name]) if protected else LOGIC_RPN[name]
        lines += [f'  | {k if k < 14 else "_"} => {ast(rpn,perm)} -- {name}']
    lines += ['', '/-- Parameters after the actual protected-phase guards. -/',
        'def guarded (k : Fin 15) (p : Fin 3 → Nat) : Fin 3 → Nat :=',
        '  if k.val < 10 then p else fun i =>',
        '    if i = 1 then p 1 else Source.safe (p i) (p 1)', '',
        '/-- Every generated expression has exactly the independently specified',
        ' schema value, including protected guards and the selected rewrites. -/',
        'theorem expression_value (k : Fin 15) (p : Fin 3 → Nat) :',
        '    eval (expression k) (guarded k p) = Source.schema k (p 0) (p 1) (p 2) := by',
        '  fin_cases k <;> rfl', '',
        'end TinyZF.Interpreter.SchemaCode', '']
    return '\n'.join(lines)


def bootstrap_source(start, edges, names):
    """Untrusted finite checkpoints, verified against the literal table in Lean."""
    index = {q: i for i, q in enumerate(names)}
    q, left, right, elapsed = start, [], [], 0
    checkpoints = []
    while q != 'main().0':
        bit = right[0] if right else '0'
        write, direction, q = edges[q, bit]
        if direction == 'R':
            left, right = [write] + left, right[1:]
        else:
            left, right = left[1:], [left[0] if left else '0', write] + right[1:]
        elapsed += 1
        if elapsed % 1000 == 0 or q == 'main().0':
            duration = elapsed - sum(row[0] for row in checkpoints)
            checkpoints.append((duration, q, ''.join(left), ''.join(right)))
        if elapsed > 100000:
            raise ValueError('bootstrap did not reach instruction entry')
    assert elapsed == 39769
    lines = ['import TinyZF.Tape.Cycles', '',
        'set_option maxRecDepth 16384', 'set_option maxHeartbeats 0', '',
        '/-! # Certified bootstrap of the literal 308-state machine', '',
        'Generated checkpoints bound kernel reduction depth. The checkpoint producer',
        'is untrusted: `checkTrace_sound` and `boot_checked` verify every literal step.',
        'No execution log, native evaluation axiom, or external prover is trusted. -/',
        'namespace TinyZF.Tape.Bootstrap', '',
        '/-- A specialized lookup for the five frequently used bootstrap states.',
        ' The fallback is the literal table, and equality is proved immediately below. -/',
        'private def fast : Machine 308 := fun q b =>',
        '  match q.val, b with']
    for state in names[:5]:
        for bit in ('0', '1'):
            w, d, target = edges[state, bit]
            nxt = 'none' if target == 'halt' else f'some {index[target]}'
            lines.append(f'  | {index[state]}, {str(bit == "1").lower()} => some ⟨{str(w == "1").lower()}, {str(d == "R").lower()}, {nxt}⟩')
    lines += ['  | _, _ => Machine308.machine q b', '',
        '/-- Specializing the bootstrap lookup does not change any transition. -/',
        'private theorem fast_eq : fast = Machine308.machine := by',
        '  funext q b', '  rcases q with ⟨q, hq⟩',
        '  cases b <;> unfold fast <;> split <;>',
        '    simp_all only [Bool.false_eq_true, Bool.true_eq_false] <;> rfl', '',
        '/-- Least-significant bits of a fixed-width binary numeral. -/',
        'private def revBits : Nat → Nat → List Bool',
        '  | 0, _ => []', '  | k+1, v => (v % 2 == 1) :: revBits k (v/2)', '',
        '/-- Finite tape prefix, preserving the specified number of leading zeros. -/',
        'private def bits (width value : Nat) : List Bool := (revBits width value).reverse', '',
        '/-- Initial finite description of the completely blank tape. -/',
        'def initial : Snapshot 308 := ⟨some 0, [], []⟩', '',
        '/-- Forty proposed segments covering the 39,769-step bootstrap. -/',
        'def checkpoints : List (Nat × Snapshot 308) := [']
    for i, (duration, q, l, r) in enumerate(checkpoints):
        comma = ',' if i + 1 < len(checkpoints) else ''
        lines.append(f'  ({duration}, ⟨some {index[q]}, bits {len(l)} {int(l or "0", 2)}, bits {len(r)} {int(r or "0", 2)}⟩){comma}')
    lines += [']', '',
        '/-- A checked segment followed by a checked tail certifies their concatenation. -/',
        'private theorem checked_cons {m : Machine 308} {s t : Snapshot 308} {k : Nat}',
        '    {rest : List (Nat × Snapshot 308)}',
        '    (h : Snapshot.run m k s = t) (hr : checkTrace m t rest = true) :',
        '    checkTrace m s ((k,t)::rest) = true := by',
        '  simp only [checkTrace, Bool.and_eq_true, decide_eq_true_eq]',
        '  exact ⟨h, hr⟩', '',
        '/-- Kernel reduction checks every proposed segment against the literal table. -/',
        'theorem boot_checked : checkTrace Machine308.machine initial checkpoints = true := by',
        '  rw [← fast_eq]', '  unfold checkpoints',
        '  repeat first | refine checked_cons (by decide +kernel) ?_ | rfl', '',
        '/-- Boot leaves a fixed unused prefix followed by zero-valued registers. -/',
        'def bootRegisters : List Nat := List.replicate 132 0 ++ 1 :: List.replicate 68 0', '',
        '/-- The initial machine reaches the interpreter entry with an 18-cell gap.',
        'This is a proof of actual tape execution, not a bounded-run assumption. -/',
        'theorem bootstrap : Exec Machine308.machine (ofConfiguration Machine308.initial)',
        '    (zc 65 [true] (zeros 18 ++ sepsR bootRegisters)) := by',
        '  have h := checkTrace_sound Machine308.machine initial checkpoints boot_checked',
        '  have hv : (traceEnd initial checkpoints).view =',
        '      zc 65 ([true] ++ zeros 8) (zeros 18 ++ sepsR bootRegisters) := by rfl',
        '  rw [hv, zc_padl] at h', '  exact h', '',
        '/-- The checked bootstrap establishes exactly the zero-register boundary',
        ' used by the unbounded primitive-program simulation. -/',
        'theorem boundary : Exec Framework.m (ofConfiguration Machine308.initial)',
        '    (Framework.boundary [] 0 18 (fun _ => 0)) := by',
        '  rw [Framework.boundary_zero]',
        '  have hr : Framework.junk ++ Framework.registers (fun _ => 0) 0 10 =',
        '      bootRegisters := by decide +kernel',
        '  simpa only [List.nil_append, hr] using bootstrap', '',
        'end TinyZF.Tape.Bootstrap', '']
    return '\n'.join(lines)

def fast_lookup_source(edges, names, index):
    """Balanced evaluator whose equality to the literal table is proved in Lean."""
    def edge(q, bit):
        e = edges.get((names[q], str(bit)))
        if e is None:
            return 'none'
        w, d, target = e
        dest = 'none' if target == 'halt' else f'some {index[target]}'
        return f'some ⟨{str(w == "1").lower()}, {str(d == "R").lower()}, {dest}⟩'
    def tree(lo, hi, indent=2):
        pad = ' ' * indent
        if hi-lo == 1:
            return [pad + f'if b then {edge(lo,1)} else {edge(lo,0)}']
        mid = (lo+hi)//2
        return ([pad + f'if q.val < {mid} then'] + tree(lo,mid,indent+2) +
                [pad+'else'] + tree(mid,hi,indent+2))
    return [
        '/-- A balanced lookup used only to accelerate certificate evaluation.',
        ' The semantic machine remains the literal table above. -/',
        'def fastLookup : Machine 308 := fun q b =>', *tree(0,308), '',
        '/-- Kernel-check every transition to justify the faster lookup. -/',
        'theorem fastLookup_eq_machine : fastLookup = machine := by',
        '  funext q b', '  fin_cases q <;> cases b <;> decide +kernel', '']


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
                '', *fast_lookup_source(edges, names, index),
                '/-- Blank tape, head at zero, original initial label `0.boot.A`. -/',
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
            'ProtectedOriginal.lean': '\n'.join(original),
            'Tape/Bootstrap.lean': bootstrap_source(start, edges, names),
            'Tape/Candidate.lean': program_source(ROOT, record),
            'Interpreter/SchemaCode.lean': schema_code_source(record),
            'Interpreter/Placement.lean': placement_source(ROOT, record),
            **graph_sources(ROOT, record)}


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
