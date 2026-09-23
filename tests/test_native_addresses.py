"""Track selected registers when address chains participate in tree search."""
import json
from pathlib import Path
import sys
import unittest
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'tools'))
from machines import ROOT
from native import build_native
from native_addresses import build_addresses
from instruction_tree import Trees
from register_check import compile_fragment
from verify_tree import equivalent_increment_cfg


class NativeAddressTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):cls.record=json.loads((ROOT/'candidates/ics-best.json').read_text())

    def test_all_source_branches_preserve_logical_registers(self):
        reference=build_native(self.record);lowered=build_addresses(self.record)
        equivalent_increment_cfg(compile_fragment(reference,reference.find_seq('main().0'),terminal='return'),
                                 compile_fragment(lowered,lowered.find_seq('main().0'),terminal='return'))

    def test_missing_overflowing_or_unconsumed_selection_rejected(self):
        m=build_addresses(self.record,compile_machine=False)
        for fragment in ('1.inc','1.decnz','1.sel',['1.sel']*(len(m.registers)+1)+['1.inc']):
            with self.assertRaises(ValueError):compile_fragment(m,fragment)

    def test_wrong_address_is_not_equivalent(self):
        m=build_addresses(self.record,compile_machine=False)
        a=compile_fragment(m,['1.sel','1.inc'])
        b=compile_fragment(m,['1.sel','1.sel','1.inc'])
        with self.assertRaises(ValueError):equivalent_increment_cfg(a,b)
        self.assertFalse(Trees().increments_only('1.inc'))

    def test_hardware_primitives_require_an_address_enabled_builder(self):
        plain=build_native(self.record,compile_machine=False)
        data={'root':0,'nodes':[['1.sel','1.inc']]}
        with self.assertRaises(ValueError):Trees().import_record(data,plain.registers)
        m=build_addresses(self.record,compile_machine=False)
        Trees().import_record(data,m.registers)


if __name__=='__main__':unittest.main()
