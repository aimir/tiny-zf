"""Emit a proposed unoptimized graph and checked increment-segment correspondence.

Python discovers witnesses only. Lean's literal path, multiset, and branch
checkers establish equivalence without trusting this extractor or optimizer.
The separate structured-source placement proof gives the unoptimized graph
its source-interpreter meaning.
"""
from collections import Counter
from functools import lru_cache
from pathlib import Path
from program_certificate import range_certificate

REGISTERS = ['prooflist', 'nextproof', 'topwff', 'wffstack', 'axiomcode',
             'param1', 'param2', 'param3', 'scratch1', 'scratch2']


def extract(machine, fragment):
    from register_check import compile_fragment
    first, cfg = compile_fragment(machine, fragment, terminal='return')
    paths = sorted(p for p, op in cfg.items() if op[0] != 'return')
    indices = {p: i for i, p in enumerate(paths)}
    def target(p):
        return indices[first if cfg[p][0] == 'return' else p]
    graph = []
    for p in paths:
        op = cfg[p]
        if op[0] == 'halt':
            graph.append(('halt',))
        elif op[0] == 'goto':
            graph.append(('jump', target(op[1])))
        else:
            graph.append((op[0], REGISTERS.index(op[1]), target(op[2]), target(op[3])))
    return target(first), graph


def matching_blocks(left, right):
    def summarize(graph):
        @lru_cache(None)
        def run(q):
            increments, successors, seen = [], [], set()
            while graph[q][0] in ('inc', 'jump'):
                if q in seen:
                    raise ValueError('increment-only loop cannot be a finite witness')
                seen.add(q)
                op = graph[q]
                if op[0] == 'inc':
                    increments.append(op[1]); q = op[2]
                else:
                    q = op[1]
                successors.append(q)
            return increments, successors, q
        return run
    ls, rs = summarize(left[1]), summarize(right[1])
    pairs = [(left[0], right[0])]
    indices = {pairs[0]: 0}
    rows = []
    def index(pair):
        if pair not in indices:
            indices[pair] = len(pairs); pairs.append(pair)
        return indices[pair]
    for lq, rq in pairs:
        lw, rw = ls(lq), rs(rq)
        lop, rop = left[1][lw[2]], right[1][rw[2]]
        assert Counter(lw[0]) == Counter(rw[0]) and lop[:2] == rop[:2]
        if lop[0] == 'halt':
            branch = ('halt',)
        else:
            assert lop[0] == 'decnz'
            branch = ('test', lop[1], index((lop[2], rop[2])), index((lop[3], rop[3])))
        rows.append((lq, rq, sorted(lw[0]), branch, lw, rw))
    return rows


def blocks(name, typ, rows):
    lines = []
    for offset in range(0, len(rows), 64):
        lines += [f'/-- Data rows {offset} through {min(offset+63,len(rows)-1)}. -/',
                  f'private def {name}{offset//64} : Array ({typ}) := #[',
                  ',\n'.join('  '+r for r in rows[offset:offset+64]), ']', '']
    lines += [f'/-- Complete ordered table of bounded data blocks. -/',
              f'private def {name}Table : Array (Array ({typ})) := #[',
              '  '+', '.join(f'{name}{i}' for i in range((len(rows)+63)//64))+']', '']
    return lines


def graph_sources(root: Path, record: dict):
    from joint import build_joint, decode
    from instruction_tree import read_record
    source = build_joint(decode(record), sharing=record['shared_operations'],
        formula_choices=record['formula_choices'], compile_machine=False, decoder=record['decoder'])
    compiled = build_joint(decode(record), sharing=record['shared_operations'], grammar=record['grammar'],
        formula_choices=record['formula_choices'], decoder=record['decoder'],
        instruction_tree=read_record(record, root/'candidates'))
    left = extract(source, source.main())
    right = extract(compiled, compiled.find_seq('main().0'))
    assert len(left[1]) == len(right[1]) == 6741
    rows = matching_blocks(left, right)
    n, m = len(left[1]), len(rows)
    header = ['set_option maxRecDepth 32768', 'set_option maxHeartbeats 0', '']
    lines = ['import TinyZF.Interpreter.Graph', '']+header+[
        '/-! # Unoptimized primitive graph used by the source proof', '',
        'Generated definitions, not a source-correctness axiom. The graph is',
        'extracted without layout optimization. Its structured source meaning',
        'must be established through `Graph.Models`; the optimized graph is',
        'related to it separately by checked increment-segment witnesses. -/',
        'namespace TinyZF.Interpreter.SourceGraph', 'open Graph', '',
        '/-- Decode a proposed successor address into the finite graph. -/',
        f'private def pc (v : Nat) : Fin {n} := ⟨v % {n}, Nat.mod_lt _ (by decide)⟩', '']
    code_rows = []
    for op in left[1]:
        if op[0] == 'halt': row = '.halt'
        elif op[0] == 'jump': row = f'.jump (pc {op[1]})'
        elif op[0] == 'inc': row = f'.inc {op[1]} (pc {op[2]})'
        else: row = f'.dec {op[1]} (pc {op[2]}) (pc {op[3]})'
        code_rows.append(row)
    lines += blocks('data', f'Graph.Instruction {n}', code_rows)
    lines += ['/-- Literal unoptimized primitive graph. -/',
              f'def program : Graph.Program {n} := fun q =>',
              '  ((dataTable[q.val/64]?.getD #[])[q.val%64]?).getD .halt', '',
              '/-- First primitive instruction, with normal iteration returns redirected here. -/',
              f'def start : Fin {n} := {left[0]}', '',
              'end TinyZF.Interpreter.SourceGraph', '']
    source_text = '\n'.join(lines)
    lines = ['import TinyZF.Interpreter.SourceGraph', 'import TinyZF.Interpreter.Segments',
             'import TinyZF.Tape.Candidate', '']+header+[
        '/-! # Checked correspondence of the current two instruction graphs', '',
        'Each row supplies a finite increment/jump path in each graph, the same',
        'per-register increments, and an identical decrement or halt. Every',
        'intermediate and target address is checked by Lean. Source semantics',
        'are a separate structured-program proof; this file proves graph',
        'equivalence without relying on the optimizer or its history. -/',
        'namespace TinyZF.Interpreter.Comparison', 'open Graph Tape.Framework', '',
        '/-- Physical primitive-graph address. -/',
        f'private def pc (v : Nat) : Fin {n} := ⟨v % {n}, Nat.mod_lt _ (by decide)⟩', '',
        '/-- Common normalized-block address. -/',
        f'private def label (v : Nat) : Fin {m} := ⟨v % {m}, Nat.mod_lt _ (by decide)⟩', '',
        '/-- One proposed correspondence, with both complete prefix witnesses. -/',
        'private structure Row where', f'  source : Fin {n}', f'  candidate : Fin {n}',
        f'  block : Block {m}', f'  sourceWitness : BlockWitness {n}',
        f'  candidateWitness : BlockWitness {n}', '',
        '/-- Decode a finite prefix witness from explicit addresses. -/',
        f'private def witness (incs successors : List Nat) (stop : Nat) : BlockWitness {n} :=',
        '  ⟨incs, successors.map pc, pc stop⟩', '']
    def ns(xs): return '['+', '.join(map(str,xs))+']'
    def ws(w): return f'witness {ns(w[0])} {ns(w[1])} {w[2]}'
    rs = []
    for lq, rq, incs, branch, lw, rw in rows:
        br = '.halt' if branch[0]=='halt' else f'.test {branch[1]} (label {branch[2]}) (label {branch[3]})'
        rs.append(f'⟨pc {lq}, pc {rq}, ⟨{ns(incs)}, {br}⟩, {ws(lw)}, {ws(rw)}⟩')
    lines += blocks('data', 'Row', rs)
    lines += ['/-- Select a correspondence row; all actual indices are checked below. -/',
        f'private def row (q : Fin {m}) : Row :=',
        '  ((dataTable[q.val/64]?.getD #[])[q.val%64]?).getD',
        '    ⟨pc 0, pc 0, ⟨[],.halt⟩, witness [] [] 0, witness [] [] 0⟩', '',
        '/-- Common decrement/halt blocks. -/', f'def common : Blocks {m} := fun q => (row q).block', '',
        '/-- Boundaries in the unoptimized graph. -/', f'def source : Fin {m} → Fin {n} := fun q => (row q).source', '',
        '/-- Corresponding boundaries in the literal candidate register graph. -/',
        f'def candidate : Fin {m} → Fin {n} := fun q => (row q).candidate', '',
        '/-- Check both proposed concrete implementations of one common block. -/',
        'def checkRow (i : Nat) : Bool :=', '  let q := label i',
        '  checkBlock SourceGraph.program common source q (row q).sourceWitness &&',
        '    checkBlock (ofTapeProgram Tape.Candidate.program) common candidate q (row q).candidateWitness', '',
        '']
    lines += range_certificate(m)
    lines += [        '/-- Both concrete prefix and branch certificates hold at every block. -/',
        f'private theorem checked_at (q : Fin {m}) :',
        '    checkBlock SourceGraph.program common source q (row q).sourceWitness = true ∧',
        '    checkBlock (ofTapeProgram Tape.Candidate.program) common candidate q (row q).candidateWitness = true := by',
        '  have h := checkRange_sound checked q.val (by omega) q.isLt',
        '  simpa only [checkRow, label, Nat.mod_eq_of_lt q.isLt, Bool.and_eq_true] using h', '',
        '/-- The source-side graph implements every common block. -/',
        'theorem source_certified : CertifiedBlocks SourceGraph.program common source :=',
        '  certifiedBlocks_of_check _ _ _ (fun q => (row q).sourceWitness) (fun q => (checked_at q).1)', '',
        '/-- The candidate graph implements exactly the same common blocks. -/',
        'theorem candidate_certified : CertifiedBlocks (ofTapeProgram Tape.Candidate.program) common candidate :=',
        '  certifiedBlocks_of_check _ _ _ (fun q => (row q).candidateWitness) (fun q => (checked_at q).2)', '',
        '/-- The actual initial graph entries are the first common block pair. -/',
        'theorem initial : source 0 = SourceGraph.start ∧ candidate 0 = Tape.Candidate.program.start := by',
        '  decide +kernel', '',
        '/-- The optimized candidate and unoptimized primitive graph have exactly',
        ' the same unbounded halting behavior from their actual zero-register starts. -/',
        'theorem candidate_iff_source : Tape.Candidate.program.Halts ↔ Halts SourceGraph.program SourceGraph.start := by',
        '  rw [← ofTapeProgram_halts]',
        '  have h := equivalent_of_blocks candidate_certified source_certified 0',
        '  simpa only [initial.1, initial.2] using h', '',
        'end TinyZF.Interpreter.Comparison', '']
    return {'Interpreter/SourceGraph.lean': source_text,
            'Interpreter/Comparison.lean': '\n'.join(lines)}
