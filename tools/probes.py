"""Bounded exploratory compiler probes. Not used to generate the accepted candidate.

Alternative factoring follows upstream's factoring approach, with a fix for
its uncalled reachable() iterator in the duplicate-sequence branch. These
experimental lowerings have no formal equivalence proof. Source logic is
unchanged, but this alone does not prove correctness of the generated TM.
"""
import argparse
from collections import defaultdict
import itertools
import json
import multiprocessing as mp
from pathlib import Path
import random
from machines import ROOT, ZF2, UPSTREAM_ORDER, build, count, totalize
from TMBuilder import subroutine
from reduce import reduce
BASE = list(UPSTREAM_ORDER)

class RandomZF2(ZF2):

    def breakout_common_subsequences(self):
        rng = random.Random(self.grammar_seed)
        search_len = max((len(s.seq) for s in self.sequences))
        while search_len > 1:
            subsequences = set()
            match = None
            reachable = list(self.reachable())
            rng.shuffle(reachable)
            for i in reachable:
                s = self.sequences[i]
                if len(s.seq) == search_len:
                    if s.seq in subsequences:
                        match = s.seq
                        break
                    subsequences.add(s.seq)
            if match:
                find = max((i for i in reachable if self.sequences[i].seq == match))
                replace = min((i for i in reachable if self.sequences[i].seq == match))
                self.sequence_lookup[self.sequences[replace].seq] = replace
                for i in reachable:
                    s = self.sequences[i].seq
                    if find in s:
                        self.sequences[i].seq = tuple((v if v != find else replace for v in s))
                        self.sequence_lookup[self.sequences[i].seq] = i
                continue
            for i in reachable:
                s = self.sequences[i]
                if len(s.seq) > search_len:
                    offsets = list(range(len(s.seq) + 1 - search_len))
                    rng.shuffle(offsets)
                    for offset in offsets:
                        subseq = s.seq[offset:offset + search_len]
                        if subseq in subsequences:
                            match = subseq
                            break
                        subsequences.add(subseq)
                if match:
                    break
            if not match:
                search_len -= 1
                continue
            match_i = self.add_sequence(match)
            for i in reachable:
                while True:
                    s = self.sequences[i].seq
                    if len(s) <= search_len:
                        break
                    for offset in range(len(s) + 1 - search_len):
                        if s[offset:offset + search_len] == match:
                            self.sequences[i].seq = s[:offset] + (match_i,) + s[offset + search_len:]
                            self.sequence_lookup[self.sequences[i].seq] = i
                            break
                    else:
                        break

class CostZF2(ZF2):

    def breakout_common_subsequences(self):
        rng = random.Random(self.grammar_seed)
        while True:
            reach = list(self.reachable())
            existing = {self.sequences[i].seq: i for i in reach}
            occ = defaultdict(list)
            for i in reach:
                seq = self.sequences[i].seq
                if len(seq) <= 2:
                    continue
                for length in range(2, min(len(seq), 32) + 1):
                    for pos in range(len(seq) - length + 1):
                        if length == len(seq):
                            continue
                        occ[seq[pos:pos + length]].append((i, pos))
            options = []
            for sub, positions in occ.items():
                length = len(sub)
                count = 0
                last_i = None
                end = -1
                for i, pos in positions:
                    if i != last_i or pos >= end:
                        count += 1
                        last_i = i
                        end = pos + length
                saving = (count - (sub not in existing)) * (length - 1)
                if saving > 0:
                    score = saving * (rng.uniform(0.65, 1.35) if self.grammar_seed else 1)
                    options.append((score, saving, length, sub))
            if not options:
                break
            _, _, _, sub = max(options, key=lambda x: x[:3])
            index = self.add_sequence(sub)
            length = len(sub)
            for i in reach:
                seq = self.sequences[i].seq
                if len(seq) <= length:
                    continue
                out = []
                pos = 0
                while pos < len(seq):
                    if seq[pos:pos + length] == sub:
                        out.append(index)
                        pos += length
                    else:
                        out.append(seq[pos])
                        pos += 1
                self.sequences[i].seq = tuple(out)
                self.sequence_lookup[tuple(out)] = i

class LowerZF2(ZF2):

    def lower(self, n):
        choice = self.choices[n - 1]
        inc = self.topwff.inc
        if choice == 0:
            if n == 1:
                return [*self.v_0(), inc]
            return [getattr(self, 'v_' + str(n - 2))(), [inc, inc]]
        if choice == 1:
            return [self.v_0(), *[inc] * n]
        if choice == 2:
            return [*self.v_0(), *[inc] * n]
        if choice == 3:
            return [getattr(self, 'v_' + str(n - 1))(), inc]
        if choice == 4:
            return [self.v_0(), self.inc_tree(n)]
        if choice == 5:
            return [*getattr(self, 'v_' + str(n - 1))(), inc]

    def inc_tree(self, n):
        if n == 1:
            return self.topwff.inc
        return [self.inc_tree(n // 2), self.inc_tree(n - n // 2)]

    @subroutine
    def v_1(self):
        return self.lower(1)

    @subroutine
    def v_2(self):
        return self.lower(2)

    @subroutine
    def v_3(self):
        return self.lower(3)

    @subroutine
    def v_4(self):
        return self.lower(4)

def evaluate(task):
    kind, config = task
    cls = {'grammar': RandomZF2, 'cost': CostZF2, 'lowering': LowerZF2}[kind]
    machine = cls()
    machine.AXIOMORDER = list(UPSTREAM_ORDER)
    if kind == 'lowering':
        machine.choices = tuple(config)
    else:
        machine.grammar_seed = config
    machine.build_machine()
    raw = count(machine.tm.states)
    final = len(reduce(totalize(machine.tm.start, machine.tm.states)))
    return (final, raw, config)

def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('kind', choices=('grammar', 'cost', 'lowering'))
    p.add_argument('--count', type=int, help='number of seeds; lowering always enumerates all 6**4 choices')
    p.add_argument('--workers', type=int, default=4)
    p.add_argument('--output', type=Path)
    args = p.parse_args()
    if args.kind == 'lowering':
        configs = list(itertools.product(range(6), repeat=4))
    else:
        configs = list(range(args.count or (2000 if args.kind == 'grammar' else 200)))
    best = None
    raw_best = None
    with mp.Pool(args.workers) as pool:
        for i, result in enumerate(pool.imap(evaluate, ((args.kind, c) for c in configs))):
            if best is None or result[0] < best[0]:
                best = result
            raw_best = result[1] if raw_best is None else min(raw_best, result[1])
            if (i + 1) % 200 == 0:
                print(f'{args.kind}: {i + 1} checked, final best {best[0]}', flush=True)
    report = {'kind': args.kind, 'evaluations': len(configs), 'order': UPSTREAM_ORDER, 'best_final_states': best[0], 'best_final_raw_states': best[1], 'best_raw_states': raw_best, 'best_config': best[2]}
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))
if __name__ == '__main__':
    main()
