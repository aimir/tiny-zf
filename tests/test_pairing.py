"""Arithmetic contracts for alternative encodings; no independence claim."""
import json
from pathlib import Path
import sys
import unittest
from types import SimpleNamespace
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'tools'))
from machines import ROOT
from pairing import build_pairing
from verify_pairing import arithmetic_checks, pair, unpair
from register_check import compile_fragment, execute
from grammar import equivalent_cfg


class PairingTests(unittest.TestCase):
    def test_numerical_and_composition_contracts(self):
        self.assertEqual(arithmetic_checks(),{'pair':1536,'unpair':12288,
            'constructors':13440,'stack':109,'guard':162,'decoder':512,'detachment':10})

    def test_extreme_numeric_round_trips_and_distinguished_codes(self):
        for a in (0,1,2,2**127+3):
            for b in (0,1,2,127):
                self.assertEqual(unpair(pair(a,b)),(a,b))
        self.assertEqual(pair(pair(0,0),0),0)
        self.assertEqual(pair(pair(0,0),1),1)
        # Enumeration decrements each nonempty proof tail before decoding it.
        for n in range(1,10000):
            self.assertLess(unpair(n-1)[1],n)

    def test_invalid_tag_permutation_rejected(self):
        r=json.loads((ROOT/'reference/pairing-experiments.json').read_text())['runs'][0]['initial']
        for order in ((1,3,4),(2,2,4),(2,3)):
            with self.assertRaises(ValueError):
                build_pairing(r,tag_order=order,compile_machine=False)

    def test_aliased_arithmetic_registers_rejected(self):
        r=json.loads((ROOT/'reference/pairing-experiments.json').read_text())['runs'][0]['initial']
        m=build_pairing(r,compile_machine=False)
        with self.assertRaises(AssertionError):m.pair(m.param1,m.param1,m.param2)
        with self.assertRaises(AssertionError):m.unpair(m.param1,m.param1,m.param2)

    def test_factoring_preserves_recoded_source(self):
        r=json.loads((ROOT/'reference/pairing-experiments.json').read_text())['runs'][0]['initial']
        r['pairing']={'kernel':'dyadic-alternating','positive_inverse':True,
                      'tags':'repeat2','tag_order':[4,2,3]}
        source=build_pairing({**r,'grammar':None},compile_machine=False);source.main()
        final=build_pairing(r)
        self.assertGreater(equivalent_cfg(
            compile_fragment(source,source.find_seq('main().0'),terminal='return'),
            compile_fragment(final,final.find_seq('main().0'),terminal='return')),0)

    def test_incumbent_tree_cannot_replace_dyadic_arithmetic(self):
        from search_pairing import inspect_source,tree_search
        from instruction_tree import read_record
        r=json.loads((ROOT/'reference/pairing-experiments.json').read_text())['runs'][0]['initial']
        r['instruction_tree']='combined-initial-tree.json'
        row=inspect_source(r);row['tree']=read_record(r,ROOT/'reference')
        args=SimpleNamespace(tree_generations=0,tree_batch=1,tree_width=4,tree_screen=1)
        with self.assertRaises(ValueError):tree_search(row,{},args,1)


if __name__=='__main__':unittest.main()
