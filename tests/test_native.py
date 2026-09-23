"""Native tape contracts and expanded-IR checks, including deliberate faults."""
from copy import deepcopy
import json
from pathlib import Path
import sys
import unittest
from unittest.mock import patch
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'tools'))
from machines import ROOT
from native import build_native,MOVE_RIGHT
from check_native import kernel_checks,source_check,literal_check
from instruction_tree import Trees
from register_check import compile_fragment,execute
from search_native import clean
from verify_tree import equivalent_increment_cfg


class NativeTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        base=json.loads((ROOT/'candidates/ics-best.json').read_text())
        cls.right=clean(base)
        cls.right['native']={'register_order':['scratch2','scratch1','topwff','wffstack','param1','param2','param3','axiomcode','prooflist','nextproof','scratch3'],
                             'moves':[['scratch1','scratch2'],['topwff','scratch1']]}
        cls.left=deepcopy(cls.right)
        cls.left['native']['register_order'][:3]=['scratch1','scratch2','topwff']
        cls.left['native']['moves']=[['scratch1','scratch2'],['scratch2','topwff']]

    def test_right_tape_kernel_preserves_every_other_register(self):
        self.assertEqual(kernel_checks(self.right,cases=1000),{'native_kernel_cases':1000})

    def test_left_tape_kernel_preserves_every_other_register(self):
        self.assertEqual(kernel_checks(self.left,cases=1000,direction='movl'),{'native_kernel_cases':1000})

    def test_kernel_checker_rejects_lost_value(self):
        broken=MOVE_RIGHT.replace('1.movr.join 0 1 L','1.movr.join 0 0 L')
        with patch('native.MOVE_RIGHT',broken),self.assertRaises(ValueError):kernel_checks(self.right,cases=30)

    def test_reordered_source_with_native_expansions_matches_original(self):
        for record in (self.right,self.left):self.assertGreater(source_check(record),0)

    def test_literal_table_matches_atomic_ir_including_native_calls(self):
        result=literal_check(build_native(self.right),checks=512)
        self.assertEqual(result['operations'],512)
        self.assertGreater(result['kinds'].get('movr',0),0)

    def test_unused_native_binding_is_not_a_native_candidate(self):
        from search_pairing import inspect_source
        record=clean(json.loads((ROOT/'candidates/ics-best.json').read_text()))
        order=record['native']['register_order']
        order.remove('axiomcode');order.insert(order.index('scratch1'),'axiomcode')
        record['native']['moves']=[['scratch1','axiomcode']]
        index=record['decoder']['order'].index('axiomcode')
        record['decoder']['stages'][index][0]='axiomcode'
        self.assertFalse(inspect_source(record,builder=build_native)['native_active'])

    def test_placement_reuses_tree_and_preserves_expanded_cfg(self):
        from place_native import placements
        original=build_native(self.right);arena=Trees();root=arena.import_machine(original)
        expected=compile_fragment(original,original.find_seq('main().0'),terminal='return')
        rows=placements(self.right,arena.export(root),width=1)
        self.assertEqual({r[3] for r in rows},{'movl','movr'})
        for record,tree,selectors,direction in rows:
            machine=build_native(record,compile_machine=False)
            current=arena.import_record(tree,machine.registers);arena.install(machine,current)
            machine.name_sequences();machine.generate();machine.tm.gc()
            count=len({q for q,b in machine.tm.states if q.startswith('3.')})
            self.assertEqual(selectors,count)
            self.assertGreater(equivalent_increment_cfg(expected,compile_fragment(machine,machine.find_seq('main().0'),terminal='return')),0)
        arena.clear_caches()

    def test_bad_layout_and_nonadjacent_transfers_fail(self):
        for native in ({'register_order':['scratch1']*11,'moves':[]},
                       {'register_order':self.right['native']['register_order'],'moves':[['scratch1','prooflist']]},
                       {'register_order':self.right['native']['register_order'],'moves':[['scratch1','scratch2']]*2}):
            with self.assertRaises(ValueError):build_native({**self.right,'native':native})
        r=deepcopy(self.right);r['decoder']['packed_counter']=True
        with self.assertRaises(ValueError):build_native(r)

    def test_unconfigured_native_tree_primitive_fails(self):
        m=build_native(self.right,compile_machine=False)
        for leaf in ('3.param1.movr','3.scratch1.movl'):
            with self.assertRaises(ValueError):Trees().import_record({'root':0,'nodes':[[leaf,'halt']]},m.registers)

    def test_native_contract_expansion_handles_zero_and_nonzero_inputs(self):
        for r in (self.right,self.left):
            m=build_native(r,compile_machine=False);leaf=m.native_opcodes['scratch1','scratch2']
            code=compile_fragment(m,leaf)
            for n in range(20):
                values,_=execute(code,{'scratch1':n,'scratch2':3,'param1':17})
                self.assertEqual(values,{'scratch1':0,'scratch2':n+3,'param1':17})

    def test_native_tree_rotations_pass_expanded_cfg_audit(self):
        m=build_native(self.right);arena=Trees();root=arena.import_machine(m)
        before=compile_fragment(m,m.find_seq('main().0'),terminal='return')
        changes=[(v,w) for v in sorted(arena.reachable(root)) for w in arena.rotations(v)]
        self.assertGreater(len(changes),100)
        for v,w in changes[::5]:
            candidate=build_native(self.right,compile_machine=False);arena.install(candidate,arena.replace(root,v,w))
            equivalent_increment_cfg(before,compile_fragment(candidate,candidate.find_seq('main().0'),terminal='return'))
        arena.clear_caches()


if __name__=='__main__':unittest.main()
