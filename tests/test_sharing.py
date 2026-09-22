"""Behavioral checks for sharing and for the compiler's finite CFG audit."""
import json
from pathlib import Path
import sys
import unittest
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'tools'))
from machines import ROOT
from joint import build_joint,decode,load_recorded,encode
from grammar import context_requirements,equivalent_cfg
from register_check import compile_fragment
from verify_sharing import sharing_checks,grammar_check


class SharingTests(unittest.TestCase):
    def test_arithmetic_sharing_preserves_all_registers(self):
        record=encode(load_recorded('ics-encoding'))
        result=sharing_checks(record)
        self.assertEqual(sum(result.values()),4280)

    def test_context_summary_agrees_with_explicit_jump_resolution(self):
        m=build_joint(load_recorded('ics-encoding'),sharing=True,compile_machine=False)
        m.main();requires=context_requirements(m)
        for i in range(len(m.sequences)):
            z,o=requires(i)
            try:
                compile_fragment(m,i)
                explicit=True
            except ValueError:
                explicit=False
            self.assertEqual(z<=1 and o==0,explicit,f'sequence {i}')

    def test_factoring_preserves_complete_control_flow(self):
        record=json.loads((ROOT/'candidates/ics-best.json').read_text())
        record['shared_operations']=True
        record.setdefault('grammar',{'kind':'random','inline_probability':.75,'seed':36})
        self.assertTrue(grammar_check(record)['distinguishes_return_and_halt'])

    def test_halt_cannot_replace_normal_completion(self):
        m=build_joint(load_recorded('ics-encoding'),compile_machine=False)
        original=compile_fragment(m,[m.param1.decnz,'halt'],terminal='return')
        altered=compile_fragment(m,[m.param1.decnz,'_break.0'],terminal='return')
        with self.assertRaisesRegex(ValueError,'different operations'):
            equivalent_cfg(original,altered)

    def test_changed_register_is_rejected(self):
        m=build_joint(load_recorded('ics-encoding'),compile_machine=False)
        a=compile_fragment(m,m.param1.inc,terminal='return')
        b=compile_fragment(m,m.param2.inc,terminal='return')
        with self.assertRaisesRegex(ValueError,'different operations'):
            equivalent_cfg(a,b)

    def test_unconditional_jump_may_be_removed(self):
        a=(0,{0:('goto',1),1:('inc','x',2,2),2:('return',)})
        b=(3,{3:('inc','x',4,4),4:('return',)})
        self.assertEqual(equivalent_cfg(a,b),2)

    def test_unconditional_divergence_cannot_be_removed(self):
        a=(0,{0:('goto',0)})
        b=(1,{1:('return',)})
        with self.assertRaisesRegex(ValueError,'different unconditional divergence'):
            equivalent_cfg(a,b)


if __name__=='__main__':unittest.main()
