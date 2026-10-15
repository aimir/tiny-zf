"""Differential integration tests against the hash-pinned Python executor.

Set MIRA254_UPSTREAM to the pinned busy-beaver checkout. No compiled library,
external source, or search log is committed; the test compiles in a temporary
directory and checks both successful and unsuccessful instruction executions.
"""
import ctypes
import os
from pathlib import Path
import random
import shutil
import subprocess
import sys
import tempfile
import unittest

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'tools'))
from compare_mira254 import recover
from mira_global import Oracle,Recording,checkpoint_identity
from mira_global_native import Engine,NativeOracle
from mira_native import compile_native,contextual_rotation,merge,MERGES
from mira_global_pairs import pair_search_identity,bootstrap_root


def converted(table):
    return {(q,int(b)):(int(w),d,'254' if t=='halt' else t)
            for (q,b),(w,d,t) in table.items()}


class NativeSymbolicTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        location=os.environ.get('MIRA254_UPSTREAM')
        if not location:raise unittest.SkipTest('set MIRA254_UPSTREAM to the pinned checkout')
        compiler=shutil.which(os.environ.get('CXX','c++'))
        if not compiler:raise unittest.SkipTest('a C++17 compiler is required')
        cls.temporary=tempfile.TemporaryDirectory()
        cls.library=Path(cls.temporary.name)/'symbolic.so'
        flags=['-dynamiclib'] if sys.platform=='darwin' else ['-shared','-fPIC']
        subprocess.run([compiler,'-std=c++17','-O3',*flags,
            str(ROOT/'tools/mira_global_native.cpp'),'-o',str(cls.library)],check=True)
        cls.python=Oracle(Path(location));cls.native=NativeOracle(cls.python,cls.library)

    @classmethod
    def tearDownClass(cls):
        cls.native.engine.close();cls.temporary.cleanup()

    def test_all_original_cases_and_exact_read_traces(self):
        self.assertEqual(self.native.check(self.python.table),(True,None))
        observed=self.native.engine.traces(self.python.table,self.python.cases)
        self.assertEqual({k:set(v)for k,v in observed.items()},
                         {k:set(v)for k,v in self.python.by_edge.items()})

    def test_changed_program_and_invalid_graft(self):
        directory=self.python.directory
        tree,root,_=recover((directory/'coq/tm/Prog254.v').read_text(),True)
        root=tree.replace(root,74,tree.node(48,63))
        python=Oracle(directory.parents[1],tree,root,converted(contextual_rotation(directory)))
        native=NativeOracle(python,self.library)
        self.assertEqual(native.check(python.table),(True,None))
        self.assertEqual(dict(native.by_edge),dict(python.by_edge))
        invalid=self.python.table.copy()
        invalid['178',0]=(0,'R','16');invalid['178',1]=(1,'R','206')
        expected=python.check(invalid)
        self.assertFalse(expected[0]);self.assertEqual(native.check(invalid),expected)

    def test_independent_263_state_decoder(self):
        directory=self.python.directory
        tree,root,_=recover((directory/'coq/tm/Prog254.v').read_text(),True)
        table=compile_native(directory,tree,root)
        for step in MERGES:table=merge(table,*step)
        candidate=converted(table)
        self.assertEqual(len(candidate)//2,263)
        self.assertEqual(self.native.check(candidate),self.python.check(candidate))
        self.assertEqual(self.native.check(candidate),(True,None))

    def test_larger_minimum_gap_uses_the_same_case_contract(self):
        python=Oracle(self.python.directory.parents[1],d0=62)
        native=NativeOracle(python,self.library)
        self.assertEqual(native.check(python.table),(True,None))
        self.assertEqual(dict(native.by_edge),dict(python.by_edge))
        self.assertNotEqual(python.cases[0],self.python.cases[0])
        with tempfile.TemporaryDirectory() as folder:
            path=Path(folder)
            checkpoint_identity(native,path)
            with self.assertRaises(ValueError):checkpoint_identity(self.native,path)

    def test_random_mutants_and_failed_execution_traces(self):
        rng=random.Random(20261015)
        names=sorted({q for q,b in self.python.table});keys=sorted(self.python.table)
        for iteration in range(1000):
            key=rng.choice(keys);edge=(rng.randrange(2),rng.choice('LR'),rng.choice(names+['254']))
            self.assertEqual(self.native.check_edge(key,edge),self.python.check_edge(key,edge),
                             (iteration,key,edge))
            if iteration>=100 or not self.python.by_edge[key]:continue
            case=self.python.by_edge[key][0];table=self.python.table.copy();table[key]=edge
            recording=Recording(table);recording.observed=set();self.python.ns['T']=recording
            try:expected=bool(self.python.run_case(case))
            finally:self.python.ns['T']=self.python.table
            self.native.engine.configure(table)
            trace=(ctypes.c_uint8*(2*self.native.engine.n))()
            actual=self.native.engine.run_case(self.python.cases[case],trace)
            seen={(self.native.engine.names[k//2],k%2)for k,v in enumerate(trace)if v}
            self.native.engine.configure(self.native.table)
            self.assertEqual(actual,expected);self.assertEqual(seen,recording.observed)

    def test_semantic_alternatives_and_case_cache(self):
        alternatives=[(('3',0),(0,'L','48')),(('9',1),(1,'L','6')),
            (('20',1),(0,'L','4')),(('42',1),(0,'R','14')),
            (('74',1),(1,'L','2')),(('33',1),(0,'L','48')),
            (('125',0),(0,'L','67'))]
        for key,edge in alternatives:
            self.assertTrue(self.python.check_edge(key,edge),(key,edge))
            self.assertTrue(self.native.check_edge(key,edge),(key,edge))
        case=self.python.cases[0]
        fresh=(list(case[0]),case[1],case[2],case[3])
        engine=self.native.engine
        self.assertEqual(engine.add_case(case),engine.add_case(fresh))
        self.assertEqual(engine.add_case(case),engine.add_case(case))

    def test_bootstrap_root_classification(self):
        root=bootstrap_root(self.python.table)
        self.assertEqual(root['status'],'unproved_root')
        self.assertEqual(root['gap'],62)
        self.assertEqual(root['registers'],[0,0,0,0,0,0,2,0,0])
        self.assertTrue(all(v==0 for v in root['trailing_registers']))


class PairCheckpointTests(unittest.TestCase):
    def test_resume_requires_same_flags_and_menu(self):
        with tempfile.TemporaryDirectory() as directory:
            folder=Path(directory);menu=folder/'options.json';menu.write_text('{}')
            pair_search_identity(folder,menu,False,False)
            pair_search_identity(folder,menu,False,False)
            for flags in [(True,False),(False,True)]:
                with self.assertRaises(ValueError):pair_search_identity(folder,menu,*flags)
            menu.write_text('{"changed":[]}')
            with self.assertRaises(ValueError):pair_search_identity(folder,menu,False,False)

    def test_legacy_offset_cannot_silently_resume(self):
        with tempfile.TemporaryDirectory() as directory:
            folder=Path(directory);menu=folder/'options.json';menu.write_text('{}')
            (folder/'progress.json').write_text('{"completed_jobs": 100}')
            with self.assertRaises(ValueError):pair_search_identity(folder,menu,False,False)


if __name__=='__main__':unittest.main()
