"""Fused arithmetic contracts, source wiring and actual native tape behavior."""
from copy import deepcopy
import json
from pathlib import Path
import sys
import unittest
from unittest.mock import patch
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'tools'))
from machines import ROOT
from native import build_native
from search_native import clean
from check_unpair import arithmetic_checks,kernel_checks,source_contract_check
from check_decoder import check
from check_native import literal_check
from unpair_fusion import FusedUnpair,CANTOR_STEP
from search_unpair import repair,category
from search_pairing import inspect_source


class FusedUnpairTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.record=clean(json.loads((ROOT/'candidates/ics-best.json').read_text()))
        cls.record['native']['unpair']={'variant':0,'restore':7,'step':True,'step_pair':['scratch1','scratch2']}
        repair(cls.record)

    def test_cantor_kernel_preserves_every_other_register(self):
        self.assertEqual(kernel_checks(self.record,cases=2000),{'kernel_cases':2000})

    def test_corrupted_cantor_kernel_is_rejected(self):
        broken=CANTOR_STEP.replace('1.cstep.second 0 1 R','1.cstep.second 0 0 R')
        with patch('unpair_fusion.CANTOR_STEP',broken),self.assertRaises(ValueError):kernel_checks(self.record,cases=10)

    def test_all_arithmetic_variants_and_restoration(self):
        for variant in range(4):
            r=deepcopy(self.record);r['native']['unpair'].update(variant=variant,step=False)
            self.assertEqual(arithmetic_checks(r,cases=120),{'unpair_cases':120,'unpair_restore_cases':120,'nonzero_output_cases':512})
        arithmetic_checks(self.record,cases=120)

    def test_broken_arithmetic_is_rejected_by_numerical_contract(self):
        def broken(self,a,b):return [a.inc,'continue_loop']
        with patch.object(FusedUnpair,'loop_body',broken),self.assertRaises(ValueError):arithmetic_checks(self.record,cases=10)

    def test_all_fusion_sites_preserve_source_wiring(self):
        for mask in range(8):
            r=deepcopy(self.record);r['native']['unpair']['restore']=mask
            self.assertGreater(source_contract_check(r),0)

    def test_corrupted_fusion_site_is_rejected(self):
        def broken(self):return [self.unpair_restore(self.scratch2,self.scratch1,self.wffstack)]
        with patch.object(FusedUnpair,'select',broken),self.assertRaises(ValueError):source_contract_check(self.record)

    def test_fused_decoder_boundaries(self):
        for eager,head_first in ((False,False),(True,True)):
            r=deepcopy(self.record);r['decoder']['eager']=eager
            for stage in r['decoder']['stages']:stage[2]=head_first
            self.assertEqual(check(r,cases=30)['boundary_cases'],30)

    def test_literal_tape_agrees_with_atomic_cantor_contract(self):
        result=literal_check(build_native(self.record),checks=512)
        self.assertGreater(result['kinds'].get('cstep',0),0)

    def test_expanding_optimized_primitives_preserves_program(self):
        from unpair_fusion import expand_native_tree
        from instruction_tree import Trees
        from register_check import compile_fragment
        from verify_tree import equivalent_increment_cfg
        old=build_native(self.record);arena=Trees();root=arena.import_machine(old)
        record,data=expand_native_tree(self.record,arena.export(root))
        new=build_native(record,compile_machine=False);root=arena.import_record(data,new.registers);arena.install(new,root)
        new.name_sequences();new.generate();new.tm.gc()
        self.assertNotIn(('1.cstep','0'),new.tm.states)
        self.assertGreater(equivalent_increment_cfg(compile_fragment(old,old.find_seq('main().0'),terminal='return'),
                                                   compile_fragment(new,new.find_seq('main().0'),terminal='return')),0)
        self.assertGreater(source_contract_check(record),0)
        arithmetic_checks(record,cases=120)
        arena.clear_caches()

    def test_default_verifier_keeps_original_arithmetic_checks(self):
        from verify_ics import verify
        report=verify(steps=1000,tree_boundaries=0)
        self.assertEqual(report['states'],json.loads((ROOT/'candidates/ics-best.json').read_text())['final_states'])
        self.assertEqual(report['arithmetic']['guard_cases'],500)

    def test_invalid_layout_and_masks_fail(self):
        r=deepcopy(self.record);r['native']['register_order'][0:2]=r['native']['register_order'][0:2][::-1]
        with self.assertRaises(ValueError):build_native(r)
        for key,value in (('restore',8),('variant',4)):
            r=deepcopy(self.record);r['native']['unpair'][key]=value
            with self.assertRaises(ValueError):build_native(r)

    def test_category_requires_emitted_cantor_kernel(self):
        row={'record':self.record,'cantor_active':False}
        self.assertEqual(category(row),'restore')
        row['cantor_active']=True;self.assertEqual(category(row),'native')
        self.assertTrue(inspect_source(self.record,builder=build_native)['cantor_active'])


if __name__=='__main__':unittest.main()
