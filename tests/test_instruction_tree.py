"""Check the tree artifact, rewrite rules, and independent CFG audit failures."""
import hashlib
import json
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'tools'))
from instruction_tree import Trees, read_record
from joint import build_joint,decode
from machines import ROOT,count
from register_check import compile_fragment
from solve_tree import canonical_words,materialize
from verify_tree import equivalent_increment_cfg,tree_check


def linear(ops,terminal='return'):
    cfg={i:('inc',name,i+1,i+1) for i,name in enumerate(ops)}
    cfg[len(ops)]=(terminal,)
    return 0,cfg


class InstructionTreeTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.record=json.loads((ROOT/'candidates/ics-best.json').read_text())
        cls.data=read_record(cls.record,ROOT/'candidates')
        options={'sharing':True,'grammar':cls.record['grammar'],
                 'formula_choices':cls.record['formula_choices'],'decoder':cls.record.get('decoder')}
        cls.source=build_joint(decode(cls.record),**options)
        cls.candidate=build_joint(decode(cls.record),**options,instruction_tree=cls.data)

    def test_increment_order_commutes(self):
        equivalent_increment_cfg(linear(['a','b','a']),linear(['b','a','a']))

    def test_changed_increment_count_or_register_fails(self):
        for changed in (['a','b'],['a','b','c']):
            with self.assertRaises(ValueError):
                equivalent_increment_cfg(linear(['a','b','a']),linear(changed))

    def test_increment_cannot_move_across_a_decrement(self):
        a=(0,{0:('inc','x',1,1),1:('decnz','x',2,2),2:('return',)})
        b=(0,{0:('decnz','x',1,1),1:('inc','x',2,2),2:('return',)})
        with self.assertRaises(ValueError):equivalent_increment_cfg(a,b)

    def test_halt_return_and_decrement_outcomes_remain_distinct(self):
        with self.assertRaises(ValueError):
            equivalent_increment_cfg(linear(['x'],'halt'),linear(['x'],'return'))
        a=(0,{0:('decnz','x',1,2),1:('halt',),2:('return',)})
        b=(0,{0:('decnz','x',2,1),1:('halt',),2:('return',)})
        with self.assertRaises(ValueError):equivalent_increment_cfg(a,b)

    def test_silent_cycle_is_rejected(self):
        with self.assertRaises(ValueError):
            equivalent_increment_cfg((0,{0:('goto',0)}),linear([]))

    def test_tree_rejects_invalid_references_and_primitives(self):
        for data in ({'root':0,'nodes':[[0,'halt']]},
                     {'root':0,'nodes':[[True,'halt']]},
                     {'root':0,'nodes':[['3.missing.inc','halt']]},
                     {'root':0,'nodes':[['arbitrary','halt']]},
                     {'root':2,'nodes':[['halt','halt']]}):
            with self.subTest(data=data),self.assertRaises(ValueError):
                Trees().import_record(data,{'x'})

    def test_tree_hash_is_checked(self):
        with tempfile.TemporaryDirectory() as directory:
            p=Path(directory)/'tree.json';p.write_text('{}')
            record={'instruction_tree':p.name,'instruction_tree_sha256':'0'*64}
            with self.assertRaisesRegex(ValueError,'hash mismatch'):read_record(record,directory)

    def test_artifact_audit_and_unchanged_native_framework(self):
        result=tree_check(self.record,self.candidate)
        self.assertGreater(result['matched_segment_pairs'],0)
        framework=lambda m:{k:v for k,v in m.tm.states.items() if k[0][0].isdigit()}
        self.assertEqual(framework(self.source),framework(self.candidate))
        self.assertEqual(count(self.candidate.tm.states),self.record['raw_states'])

    def test_all_single_rewrites_at_incumbent_pass_the_cfg_audit(self):
        tree=Trees();root=tree.import_record(self.data,self.source.registers)
        before=compile_fragment(self.candidate,self.candidate.find_seq('main().0'),terminal='return')
        changes=[(v,w) for v in tree.reachable(root) for w in tree.rotations(v)]
        self.assertGreater(len(changes),200)
        for v,w in changes:
            changed=tree.replace(root,v,w)
            m=build_joint(decode(self.record),decoder=self.record.get('decoder'),compile_machine=False);tree.install(m,changed)
            after=compile_fragment(m,m.find_seq('main().0'),terminal='return')
            equivalent_increment_cfg(before,after)
        tree.clear_caches()

    def test_closed_word_grammar_round_trip(self):
        tree=Trees();root=tree.import_record(self.data,self.source.registers)
        atoms,productions,required,rootword,words=canonical_words(tree,root,4)
        other,newroot=materialize(atoms,productions,rootword)
        m=build_joint(decode(self.record),decoder=self.record.get('decoder'),compile_machine=False);other.install(m,newroot)
        a=compile_fragment(self.candidate,self.candidate.find_seq('main().0'),terminal='return')
        b=compile_fragment(m,m.find_seq('main().0'),terminal='return')
        equivalent_increment_cfg(a,b)
        tree.clear_caches();other.clear_caches()
        # Solver workers can propose long right spines before finding a compact
        # grammar. Building these must not consume the Python/C call stack.
        longword=(0,)*700
        productions={(0,)*n:((0,),(0,)*(n-1)) for n in range(2,701)}
        longtree,longroot=materialize([('leaf','3.x.inc')],productions,longword)
        self.assertEqual(len(longtree.reachable(longroot)),699)
        longtree.clear_caches()


if __name__=='__main__':unittest.main()
