"""Check safe fragment transfer and source/tree separation in combined search."""
import json
from pathlib import Path
import random
import sys
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]/'tools'))
from instruction_tree import Trees, read_record
from machines import ROOT
from register_check import compile_fragment
from search_combined import (build_source, cfg_signature, compile_tree, diverse_select,
                             fragment_bank, gene_of, mutate, optimize, screen_source,
                             source_record, transfer_fragments)
from verify_tree import equivalent_increment_cfg


def linear(ops, terminal='return'):
    cfg = {i: ('inc', name, i+1, i+1) for i, name in enumerate(ops)}
    cfg[len(ops)] = (terminal,)
    return 0, cfg


class CombinedSearchTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.record = json.loads((ROOT/'candidates/ics-best.json').read_text())
        cls.data = read_record(cls.record, ROOT/'candidates')
        cls.gene = gene_of(cls.record)
        cls.bank = fragment_bank(cls.data)

    def test_gene_round_trip_and_independent_inlining_seed(self):
        record = source_record(self.gene)
        record['grammar']['inline_seed'] = 912
        record['grammar']['inline_main'] = True
        self.assertEqual(source_record(gene_of(record)), record)
        self.assertNotIn('instruction_tree', record)
        rng = random.Random(73)
        for _ in range(100):
            changed = mutate(self.gene, rng)
            self.assertEqual(gene_of(source_record(changed)), changed)

    def test_fragment_key_preserves_branch_order_and_exits(self):
        self.assertEqual(cfg_signature(linear(['a','b','a'])), cfg_signature(linear(['b','a','a'])))
        self.assertNotEqual(cfg_signature(linear(['a'])), cfg_signature(linear(['b'])))
        self.assertNotEqual(cfg_signature(linear([], 'halt')), cfg_signature(linear([])))
        a = (0, {0: ('decnz','x',1,2), 1: ('halt',), 2: ('return',)})
        b = (0, {0: ('decnz','x',2,1), 1: ('halt',), 2: ('return',)})
        self.assertNotEqual(cfg_signature(a), cfg_signature(b))
        with self.assertRaises(ValueError): cfg_signature((0, {0: ('goto',0)}))

    def test_transfer_to_changed_source_preserves_its_cfg(self):
        record = source_record(self.gene)
        record['formula_choices']['ICS'] = (record['formula_choices']['ICS']+1) % 256
        gene = gene_of(record); source = build_source(gene)
        arena = Trees(); root = arena.import_machine(source)
        changed, matches = transfer_fragments(arena, root, self.bank)
        self.assertGreater(matches, 0)
        after = compile_tree(gene, arena, changed)
        a = compile_fragment(source, source.find_seq('main().0'), terminal='return')
        b = compile_fragment(after, after.find_seq('main().0'), terminal='return')
        equivalent_increment_cfg(a,b)
        # A complete old tree must fail against this genuinely changed source.
        stale = arena.import_record(self.data, source.registers)
        old = compile_tree(gene, arena, stale)
        with self.assertRaises(ValueError):
            equivalent_increment_cfg(a, compile_fragment(old, old.find_seq('main().0'), terminal='return'))
        arena.clear_caches()

    def test_saved_tree_survives_source_rebuild_and_full_frontier_scoring(self):
        row = screen_source(self.gene); row['trees'] = [self.data]
        settings = {'mode':'general', 'tree_width':4, 'tree_batch':8, 'tree_keep':2, 'edge_rewrites':True}
        result = optimize((row, None, settings, 317, 2))
        self.assertLessEqual(result['final_states'], self.record['final_states'])
        self.assertGreaterEqual(result['last_reduced_trees'], 4)
        self.assertEqual(len(result['trees']), 2)
        self.assertEqual(result['last_tree_attempts'], 16)

    def test_final_reduced_score_can_reverse_the_raw_ranking(self):
        row = screen_source(self.gene); row['trees'] = [self.data]
        source_size = row['source_states']
        self.assertGreater(source_size, self.record['raw_states'])
        settings = {'mode':'general', 'tree_width':4, 'tree_batch':8, 'tree_keep':2, 'edge_rewrites':False}
        # Deliberately invert the score; no synthetic result is saved as an artifact.
        with patch('search_combined.reduce', side_effect=lambda rows: range(1 if len(rows)==source_size else 2)):
            result = optimize((row, None, settings, 317, 0))
        self.assertEqual(result['final_states'], 1)
        self.assertEqual(result['raw_states'], source_size)

    def test_diversity_keeps_quality_and_distinct_families(self):
        rows = [(1,'a'), (2,'a'), (3,'a'), (4,'b'), (5,'c'), (6,'d')]
        kept = diverse_select(rows, 4, lambda r:r[0], lambda r:r[1])
        self.assertEqual(kept, [(1,'a'), (2,'a'), (4,'b'), (5,'c')])


if __name__ == '__main__': unittest.main()
