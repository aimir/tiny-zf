"""Independent decoder contracts, live-value safety, and saved-tree preservation."""
from copy import deepcopy
import itertools
import json
from pathlib import Path
import sys
import unittest
from types import SimpleNamespace
from unittest.mock import patch

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'tools'))
from machines import ROOT
from decoder import FIELDS, allocation_plan, build_decoder, default_options
from check_decoder import check, check_plan, pair, unpair
from search_decoder import grid, run
from search_pairing import inspect_source, tree_search
from instruction_tree import read_record


class DecoderTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.record=json.loads((ROOT/'candidates/ics-best.json').read_text())

    def test_symbolic_resource_contract_for_every_grid_plan(self):
        records=list(grid(self.record))
        self.assertEqual(len(records),1024)
        for record in records:
            self.assertGreater(check_plan(record['decoder']),0)

    def test_invalid_alias_live_value_and_field_orders_rejected(self):
        bad=[]
        o=default_options();o['order']=['param1']*4;bad.append(o)
        o=default_options();o['clear_order']=['param1']*4;bad.append(o)
        o=default_options();o['stages'][0][0]='prooflist';bad.append(o)
        o=default_options();o['stages'][0][1]='scratch1';bad.append(o)
        o=default_options();o['stages'][1][0]='axiomcode';bad.append(o)
        o=default_options();o['stages'][0][0]=-1;bad.append(o)
        for options in bad:
            with self.subTest(options=options),self.assertRaises(ValueError):allocation_plan(options)
        with self.assertRaises(ValueError):
            build_decoder({**self.record,'decoder':{**default_options(),'packed_counter':True,'borrow_stack':True}})

    def test_symbolic_audit_rejects_corrupt_plan(self):
        good=allocation_plan(default_options())
        for broken in (good+[('clear','param1')],good+[('move','param1','param2')],
                       [('unpair','scratch1','scratch2','param1')]+good,good[:-1]):
            with patch('check_decoder.allocation_plan',return_value=broken),self.assertRaises(ValueError):
                check_plan(default_options())

    def test_boundary_contract_for_direct_rotating_and_deferred_allocations(self):
        records=list(grid(self.record))
        for index in (0,1,4,14,29,63,96,127,512,600,800,1023):
            for packed,borrow in ((False,False),(True,False),(False,True)):
                r=deepcopy(records[index]);r['decoder'].update(packed_counter=packed,borrow_stack=borrow)
                result=check(r,cases=20,seed=801+index)
                self.assertEqual(result['boundary_cases'],20)
                self.assertGreater(result['unchanged_body_cfg_pairs'],0)

    def test_current_winner_boundary_contract(self):
        self.assertEqual(check(self.record,cases=100)['boundary_cases'],100)

    def test_field_permutation_encoding_and_positive_tail_round_trip(self):
        # Pure integer coding test, independent of register lowering. One
        # instruction stores four heads followed by a zero or positive tail.
        for order in itertools.permutations(FIELDS):
            for values in itertools.product(range(2),repeat=4):
                fields=dict(zip(FIELDS,values))
                for tail in (0,1,6):
                    n=tail
                    for name in reversed(order):n=pair(fields[name],n)
                    decoded={}
                    for name in order:decoded[name],n=unpair(n)
                    self.assertEqual((decoded,n),(fields,tail))
        # Subtracting one from a nonempty continuation makes the next code
        # smaller, even when all four heads are zero.
        for n in range(1,10000):
            tail=n-1
            for _ in range(4):_,tail=unpair(tail)
            self.assertLess(tail,n)

    def test_old_whole_program_tree_cannot_replace_new_decoder(self):
        row=inspect_source(self.record,builder=build_decoder)
        old=json.loads((ROOT/'reference/combined-experiments.json').read_text())['runs'][0]['initial']
        old['instruction_tree']='combined-initial-tree.json'
        row['tree']=read_record(old,ROOT/'reference')
        args=SimpleNamespace(tree_generations=0,tree_width=4,tree_batch=1,tree_screen=1)
        with self.assertRaises(ValueError):tree_search(row,{},args,1,builder=build_decoder)

    def test_restart_scores_saved_tree_before_source_selection(self):
        import tempfile
        with tempfile.TemporaryDirectory() as directory:
            path=Path(directory);frontier=path/'frontier.json'
            tree=read_record(self.record,ROOT/'candidates')
            frontier.write_text(json.dumps([{'record':self.record,'tree':tree}]))
            args=SimpleNamespace(initial=ROOT/'candidates/ics-best.json',output=path/'result.json',
                resume_frontier=frontier,borrow_stack=False,packed_counter=False,seed=7,
                generations=0,batch=1,width=4,tree_candidates=1,tree_generations=0,
                tree_batch=1,tree_width=4,tree_screen=1,memory_mb=512)
            run(args)
            saved=json.loads(args.output.read_text())
            self.assertLessEqual(saved['final_states'],self.record['final_states'])
            self.assertEqual(saved['decoder'],self.record['decoder'])
            self.assertEqual(saved['table_sha256'],self.record['table_sha256'])
            self.assertEqual(saved['active_registers'],self.record['active_registers'])
            self.assertEqual(saved['framework_states']+saved['dag_states'],saved['raw_states'])

    def test_packed_counter_removes_physical_register(self):
        r=deepcopy(self.record);r['decoder']['packed_counter']=True
        m=build_decoder(r)
        active={q.split('.')[1] for q,b in m.tm.states if q.startswith('3.')}
        self.assertEqual(len(active),9)
        self.assertNotIn('nextproof',active)
        self.assertNotIn('scratch3',active)


if __name__=='__main__':unittest.main()
