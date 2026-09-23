"""Alternate source mutations and instruction-tree search using final TM scores.

Each source owns its tree frontier. New source mutations are rebuilt, then may
reuse closed fragments from a donor tree only when their normalized CFGs match.
All surviving trees pass the independent whole-program CFG audit. Raw counts
screen new sources and tree mutations; every completed tree frontier receives
full reduction before selecting source survivors. Search artifacts are raw TMs.
"""
import argparse
from collections import Counter, deque
from functools import lru_cache
import hashlib
import json
import multiprocessing as mp
from pathlib import Path
import random
import resource
import sys
import gc
from types import SimpleNamespace

from formula_rewrite import LIMITS, check_choices
from instruction_tree import Trees, read_record
from joint import build_joint, decode, encode
from machines import ROOT, count, totalize, write_table
from reduce import reduce
from register_check import compile_fragment
from search_joint import mutation
from search_rewrites import NAMES, formula_choices
from verify_tree import equivalent_increment_cfg

PROBABILITIES = (None, 0., .25, .5, .75, 1.)
MEMORY_MB = 0


def check_memory():
    peak = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    peak_mb = peak / (1024**2 if sys.platform == "darwin" else 1024)
    if MEMORY_MB and peak_mb > MEMORY_MB:
        raise MemoryError(f"worker resident-memory budget exceeded: {peak_mb:.0f} MiB")
    return peak_mb


def gene_of(record):
    grammar = record['grammar']
    return (decode(record), tuple(record.get('formula_choices', {}).get(n, -1) for n in NAMES),
            (grammar['kind'], PROBABILITIES.index(grammar.get('inline_probability')),
             grammar['seed'], grammar.get('inline_main', True),
             grammar.get('inline_seed', grammar['seed'])))


def source_record(gene):
    config, choices, (kind, probability, seed, main, inline_seed) = gene
    return {**encode(config), 'formula_choices': formula_choices(choices), 'shared_operations': True,
            'grammar': {'kind': kind, 'inline_probability': PROBABILITIES[probability],
                        'seed': seed, 'inline_main': main, 'inline_seed': inline_seed}}


def build_source(gene):
    r = source_record(gene)
    return build_joint(gene[0], sharing=True, grammar=r['grammar'], formula_choices=r['formula_choices'])


def mutate(gene, rng):
    config, choices, grammar = gene
    kind = rng.randrange(16)
    if kind < 6:
        choices = list(choices)
        for _ in range(1 if kind < 5 else 3):
            j = rng.randrange(len(NAMES)); choices[j] = rng.randrange(-1, LIMITS[NAMES[j]])
        choices = tuple(choices)
    elif kind < 12:
        config = mutation(config, rng, encoding_search=True)
    else:
        method, p, seed, main, inline_seed = grammar
        if kind == 12: p = rng.randrange(len(PROBABILITIES))
        elif kind == 13: seed = rng.randrange(2**24)
        elif kind == 14: inline_seed = rng.randrange(2**24)
        elif rng.randrange(4): method = rng.choice(('cost', 'random', 'pair'))
        else: main = not main
        grammar = method, p, seed, main, inline_seed
    return config, choices, grammar


def fingerprint(data):
    return hashlib.sha256(json.dumps(data, separators=(',', ':')).encode()).hexdigest()


def cfg_signature(compiled):
    """Conservative canonical graph key; differing keys need not mean inequivalence.

    Hide jumps and collect increments until the next decrement/exit. Number
    reachable segment entries by ordered traversal. Exact equality implies the
    segment bisimulation checked independently by equivalent_increment_cfg.
    """
    entry, cfg = compiled
    indices = {entry: 0}; todo = deque([entry]); rows = []
    while todo:
        pc = todo.popleft(); seen = set(); increments = Counter()
        while cfg[pc][0] in ('goto', 'inc'):
            if pc in seen: raise ValueError('silent/increment cycle has no fragment signature')
            seen.add(pc); op = cfg[pc]
            if op[0] == 'goto': pc = op[1]
            else:
                if op[2] != op[3]: raise ValueError('increment has unequal successors')
                increments[op[1]] += 1; pc = op[2]
        op = cfg[pc]; row = [tuple(sorted(increments.items())), op[:2]]
        if op[0] == 'decnz':
            targets = []
            for target in op[2:]:
                if target not in indices:
                    indices[target] = len(indices); todo.append(target)
                targets.append(indices[target])
            row.append(tuple(targets))
        elif op[0] not in ('return', 'halt'): raise ValueError('unknown fragment operation')
        rows.append(tuple(row))
    return tuple(rows)


def fragment_bank(data):
    """Index reusable closed fragments of one donor, with bounded fragment size."""
    arena = Trees(); root = arena.import_record(data)
    holder = SimpleNamespace(sequences=[SimpleNamespace(seq=p) for p in arena.nodes])
    bank = {}
    for v in sorted(arena.reachable(root)):
        n = len(arena.reachable(v))
        if not 2 <= n <= 70 or not arena.closed(v): continue
        compiled = compile_fragment(holder, v, terminal='return')
        if len(compiled[1]) > 1500: continue
        try: key = cfg_signature(compiled)
        except ValueError: continue
        old = bank.get(key)
        if old is None or len(old['nodes']) > n: bank[key] = arena.export(v)
    arena.clear_caches()
    return bank


def transfer_fragments(arena, root, bank):
    """Replace only closed subtrees with matching register operations and exits."""
    holder = SimpleNamespace(sequences=[SimpleNamespace(seq=p) for p in arena.nodes])
    replacements = {}
    for v in sorted(arena.reachable(root)):
        if not 2 <= len(arena.reachable(v)) <= 70 or not arena.closed(v): continue
        compiled = compile_fragment(holder, v, terminal='return')
        if len(compiled[1]) > 1500: continue
        try: key = cfg_signature(compiled)
        except ValueError: continue
        if key in bank:
            w = arena.import_record(bank[key])
            if w != v: replacements[v] = w
    @lru_cache(None)
    def visit(v):
        if v in replacements: return replacements[v]
        if not isinstance(v, int): return v
        return arena.node(*(visit(x) for x in arena.nodes[v]))
    return visit(root), len(replacements)


def screen_source(gene):
    check_memory()
    machine = build_source(gene)
    arena = Trees(); root = arena.import_machine(machine)
    data = arena.export(root); arena.clear_caches()
    return {'gene': gene, 'source_states': count(machine.tm.states), 'source_hash': fingerprint(data)}


def compile_tree(gene, arena, root):
    machine = build_joint(gene[0], compile_machine=False)
    arena.install(machine, root); machine.name_sequences(); machine.generate(); machine.tm.gc()
    return machine


def optimize(job):
    """One bounded tree search; fully reduce the complete final tree frontier."""
    candidate, donor, settings, seed, rounds = job
    gene = candidate['gene']; machine = build_source(gene)
    original = compile_fragment(machine, machine.find_seq('main().0'), terminal='return')
    arena = Trees(settings['mode'], True, 1); source_root = arena.import_machine(machine)
    fixed = count(machine.tm.states) - arena.size(source_root)
    roots = [arena.import_record(data, machine.registers) for data in candidate.get('trees', [])]
    roots.append(source_root)
    transferred = 0
    if donor is not None:
        newroot, transferred = transfer_fragments(arena, source_root, fragment_bank(donor))
        if newroot != source_root: roots.append(newroot)
    roots = list(dict.fromkeys(roots)); rng = random.Random(seed)
    roots.sort(key=arena.size); beam = roots[:settings['tree_width']]
    mutation_attempts = 0
    for _ in range(rounds):
        trials = set(beam)
        moves = {}
        for _ in range(settings['tree_batch']):
            current = rng.choice(beam)
            for _ in range(1 if rng.randrange(4) else rng.randrange(2, 5)):
                choices = []
                for v in sorted(arena.reachable(current)):
                    if v not in moves: moves[v] = tuple(arena.rotations(v))
                    choices.extend((v, w) for w in moves[v])
                if not choices: break
                v, w = rng.choice(choices)
                if settings['edge_rewrites'] and rng.randrange(4) == 0:
                    parents = [p for p in sorted(arena.reachable(current)) if v in arena.nodes[p]]
                    if parents:
                        parent = rng.choice(parents); a, b = arena.nodes[parent]
                        w = arena.node(w if a == v else a, w if b == v else b); v = parent
                current = arena.replace(current, v, w)
            trials.add(current); mutation_attempts += 1
        scored = [(arena.size(v), v) for v in sorted(trials)]
        rng.shuffle(scored); scored.sort(key=lambda x: x[0])
        width = settings['tree_width']; beam = []
        # Retain near-best candidates, so a temporarily larger tree can survive.
        for offset, quota in ((0, max(1, width//2)), (1, width//4), (2, width//4)):
            beam.extend([v for s, v in scored if s == scored[0][0]+offset][:quota])
        beam.extend(v for _, v in scored if v not in beam and len(beam) < width)
        old = arena; arena, beam = old.compact(beam); old.clear_caches()
        check_memory()
    # A saved finalist can have a better reduced score despite a worse raw score.
    # Preserve it through every raw screening stage.
    beam = list(dict.fromkeys([*beam, *(arena.import_record(d, machine.registers)
                                      for d in candidate.get('trees', []))]))
    results = []
    for root in beam:
        m = compile_tree(gene, arena, root); raw = count(m.tm.states)
        if raw != arena.size(root)+fixed: raise ValueError('raw state-count model mismatch')
        final = len(reduce(totalize(m.tm.start, m.tm.states)))
        results.append((final, raw, root, m))
    rng.shuffle(results); results.sort(key=lambda row: row[:2])
    kept = results[:settings['tree_keep']]
    for _, _, root, m in kept:
        equivalent_increment_cfg(original, compile_fragment(m, m.find_seq('main().0'), terminal='return'))
    best = kept[0]
    result = {**candidate, 'source_states': count(machine.tm.states), 'final_states': best[0],
              'raw_states': best[1], 'trees': [arena.export(row[2]) for row in kept],
              'last_tree_attempts': mutation_attempts, 'last_reduced_trees': len(results),
              'last_transferred_fragments': transferred, 'worker_peak_mb': check_memory()}
    arena.clear_caches(); gc.collect()
    return result


def diverse_select(rows, limit, score, signature):
    """Half quality slots, then one per structural family, then fill by quality."""
    ordered = sorted(rows, key=score); selected = ordered[:max(1, limit//2)]
    families = {signature(row) for row in selected}
    for row in ordered[len(selected):]:
        if len(selected) >= limit: break
        family = signature(row)
        if family not in families: selected.append(row); families.add(family)
    for row in ordered:
        if len(selected) >= limit: break
        if not any(row is old for old in selected): selected.append(row)
    return selected


def family(row):
    config, choices, grammar = row['gene']
    return choices, config[2:], grammar[0:2], grammar[3]


def worker_limit(memory_mb):
    # macOS does not reliably support lowering RLIMIT_AS. Check RSS at each
    # tree generation instead; this is a cooperative budget, not an OS cap.
    global MEMORY_MB
    MEMORY_MB = memory_mb
    check_memory()


def save(candidate, initial, path, summary):
    r = {k: initial[k] for k in ('wade_commit', 'ics_formula_commit') if k in initial}
    r.update(source_record(candidate['gene']))
    tree_path = path.with_suffix('.tree.json')
    tree_path.write_text(json.dumps(candidate['trees'][0], indent=2)+'\n')
    arena = Trees(); root = arena.import_record(candidate['trees'][0])
    machine = compile_tree(candidate['gene'], arena, root); arena.clear_caches()
    check_choices(r['formula_choices'])
    from verify_tree import tree_check
    checked = tree_check(r, machine)
    table = path.with_suffix('.tm'); write_table(table, machine)
    names = {q for q, b in machine.tm.states}
    r.update(kind='ics-combined-search', status='experimental; not formally verified',
             raw_states=count(machine.tm.states), final_states=candidate['final_states'],
             framework_states=sum(q[0].isdigit() for q in names),
             dag_states=sum(not q[0].isdigit() for q in names),
             active_registers=len({q.split('.')[1] for q in names if q.startswith('3.')}),
             instruction_tree=tree_path.name, instruction_tree_sha256=hashlib.sha256(tree_path.read_bytes()).hexdigest(),
             table_sha256=hashlib.sha256(table.read_bytes()).hexdigest(), combined_search=summary,
             matched_segment_pairs=checked['matched_segment_pairs'])
    path.write_text(json.dumps(r, indent=2)+'\n')


def run(args):
    initial = json.loads(args.initial.read_text())
    if initial.get('decoder'):raise ValueError('decoder allocation present: use search_decoder.py to preserve it')
    gene = gene_of(initial)
    if not initial.get('shared_operations') or not gene[0][4]:
        raise ValueError('combined search requires the shared two-scratch source')
    args.output.parent.mkdir(parents=True, exist_ok=True)
    tree = read_record(initial, args.initial.parent)
    settings = {key: getattr(args, key) for key in ('mode', 'tree_width', 'tree_batch', 'tree_keep', 'edge_rewrites')}
    first = screen_source(gene)
    if tree: first['trees'] = [tree]
    champion = optimize((first, None, settings, args.seed, 0))
    beam = [champion]; boot_results = [champion]
    seen = {gene}; seen_trees = {first['source_hash']}
    if args.initial_frontier:
        for record in json.loads(args.initial_frontier.read_text()):
            other_gene = gene_of(record)
            existing = next((r for r in beam if r['gene'] == other_gene), None)
            data = [*(existing['trees'] if existing else []), *record['trees']]
            other = screen_source(other_gene)
            other['trees'] = list({fingerprint(d): d for d in data}.values())
            if existing is not None: beam.remove(existing)
            restored = optimize((other, None, settings, args.seed, 0))
            beam.append(restored); boot_results.append(restored)
            seen.add(other_gene); seen_trees.add(other['source_hash'])
        beam = diverse_select(beam, args.width, lambda r: (r['final_states'], r['raw_states']), family)
        champion = min(beam, key=lambda r: (r['final_states'], r['raw_states']))
    rng = random.Random(args.seed); history = []
    summary = {'seed': args.seed, 'settings': {**settings, **{k: getattr(args, k) for k in
               ('batch', 'width', 'shortlist', 'tree_rounds', 'deep_rounds', 'deep_count', 'screen_slack', 'workers', 'memory_mb', 'parent_donors', 'exploration_slots')}},
               'initial_states': champion['final_states'], 'generations': 0, 'source_evaluations': len(seen),
               'initial_frontier_sources': len(beam), 'tree_searches': len(boot_results), 'tree_mutation_attempts': 0,
               'fully_reduced_trees': sum(r['last_reduced_trees'] for r in boot_results),
               'transferred_fragment_matches': 0, 'history': history}
    save(champion, initial, args.output, summary)
    context = mp.get_context('spawn')
    with context.Pool(args.workers, initializer=worker_limit, initargs=(args.memory_mb,)) as pool:
        for generation in range(args.generations):
            batch = set(); parents = {}
            while len(batch) < args.batch:
                parent = rng.choice(beam)
                changed = mutate(parent['gene'], rng)
                if changed not in seen and changed not in batch:
                    batch.add(changed); parents[changed] = parent['trees'][0]
            seen.update(batch)
            screened = pool.map(screen_source, sorted(batch, key=repr))
            unique = []
            for row in screened:
                if row['source_hash'] not in seen_trees:
                    seen_trees.add(row['source_hash']); unique.append(row)
            if unique:
                floor = min(row['source_states'] for row in unique)
                eligible = [row for row in unique if row['source_states'] <= floor+args.screen_slack]
                shortlist = diverse_select(eligible, args.shortlist-args.exploration_slots,
                                           lambda r: r['source_states'], family)
                if args.exploration_slots:
                    selected = {r['gene'] for r in shortlist}
                    others = [r for r in unique if r['gene'] not in selected]
                    # Reserve trials for other arithmetic/factoring families even
                    # when their raw compiler size fails the ordinary screen.
                    shortlist += diverse_select(others, args.exploration_slots,
                                                 lambda r: r['source_states'],
                                                 lambda r: (r['gene'][0][3:], r['gene'][2][:2]))
            else: shortlist = []
            donor = champion['trees'][0]
            tasks = [(row, parents[row['gene']] if args.parent_donors else donor,
                      settings, rng.randrange(2**32), args.tree_rounds) for row in shortlist]
            # Revisit each surviving source's saved trees rather than resetting it.
            tasks.extend((row, None, settings, rng.randrange(2**32), args.tree_rounds) for row in beam)
            print(f'generation {generation+1}: optimizing {len(shortlist)} new sources and {len(beam)} survivors', flush=True)
            optimized = pool.map(optimize, tasks, chunksize=1)
            def tally(rows):
                summary['peak_worker_mb'] = max(summary.get('peak_worker_mb', 0), *(r['worker_peak_mb'] for r in rows))
                summary['tree_searches'] += len(rows)
                summary['tree_mutation_attempts'] += sum(r['last_tree_attempts'] for r in rows)
                summary['fully_reduced_trees'] += sum(r['last_reduced_trees'] for r in rows)
                summary['transferred_fragment_matches'] += sum(r['last_transferred_fragments'] for r in rows)
            tally(optimized)
            contenders = diverse_select(optimized, args.deep_count, lambda r: (r['final_states'], r['raw_states']), family)
            if args.deep_rounds:
                print(f'generation {generation+1}: deepening {len(contenders)} sources; short-search best {min(r["final_states"] for r in optimized)}', flush=True)
                deep = pool.map(optimize, [(row, donor, settings, rng.randrange(2**32), args.deep_rounds) for row in contenders], chunksize=1)
                tally(deep)
                improvements = {row['gene']: row for row in deep}
                optimized = [improvements.get(row['gene'], row) for row in optimized]
            rng.shuffle(optimized)
            beam = diverse_select(optimized, args.width, lambda r: (r['final_states'], r['raw_states']), family)
            best = min(beam, key=lambda r: (r['final_states'], r['raw_states']))
            if (best['final_states'], best['raw_states']) < (champion['final_states'], champion['raw_states']):
                champion = best
                history.append({'generation': generation+1, 'states': best['final_states'], 'source_states': best['source_states']})
            summary.update(generations=generation+1, source_evaluations=len(seen), distinct_source_trees=len(seen_trees))
            save(champion, initial, args.output, summary)
            # Large frontiers are scratch artifacts, never part of the curated results.
            frontier = [{**source_record(row['gene']), **{k: v for k, v in row.items() if k != 'gene'}} for row in beam]
            args.output.with_suffix('.frontier.json').write_text(json.dumps(frontier)+'\n')
            print(f"generation {generation+1}: best {champion['final_states']}; final frontier "
                  f"{min(r['final_states'] for r in beam)}..{max(r['final_states'] for r in beam)}; "
                  f"{len(seen)} source evaluations, {summary['tree_mutation_attempts']} tree attempts", flush=True)
    return summary


def parser():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--initial', type=Path, default=ROOT/'candidates/ics-best.json')
    p.add_argument('--initial-frontier', type=Path, help='resume source/tree survivors from a scratch frontier')
    p.add_argument('--parent-donors', action='store_true', help='transfer fragments from each mutation parent')
    p.add_argument('--output', type=Path, default=ROOT/'scratch/combined.json')
    p.add_argument('--seed', type=int, default=20261010)
    p.add_argument('--generations', type=int, default=12)
    p.add_argument('--batch', type=int, default=128)
    p.add_argument('--width', type=int, default=12)
    p.add_argument('--shortlist', type=int, default=16)
    p.add_argument('--screen-slack', type=int, default=8)
    p.add_argument('--exploration-slots', type=int, default=0, help='shortlist slots exempt from the raw-size cutoff')
    p.add_argument('--tree-rounds', type=int, default=24)
    p.add_argument('--tree-batch', type=int, default=96)
    p.add_argument('--tree-width', type=int, default=24)
    p.add_argument('--tree-keep', type=int, default=4)
    p.add_argument('--deep-rounds', type=int, default=100)
    p.add_argument('--deep-count', type=int, default=4)
    p.add_argument('--mode', choices=('basic', 'continue', 'general'), default='general')
    p.add_argument('--edge-rewrites', action='store_true')
    p.add_argument('--workers', type=int, default=2)
    p.add_argument('--memory-mb', type=int, default=768, help='cooperative per-worker resident-memory budget in MiB; 0 disables')
    return p


if __name__ == '__main__':
    p = parser(); args = p.parse_args()
    if min(args.generations, args.batch, args.width, args.shortlist, args.tree_batch,
           args.tree_width, args.tree_keep, args.deep_count, args.workers) < 1:
        p.error('search sizes must be positive')
    if min(args.tree_rounds, args.deep_rounds, args.screen_slack, args.memory_mb, args.exploration_slots) < 0:
        p.error('rounds, slack and memory must be nonnegative')
    if args.exploration_slots >= args.shortlist: p.error('exploration-slots must be less than shortlist')
    if args.tree_keep > args.tree_width: p.error('tree-keep cannot exceed tree-width')
    run(args)
