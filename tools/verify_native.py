"""Check ordinary native transfers or the separate exposed-address experiment."""
import argparse
import hashlib
import json
from pathlib import Path
from machines import ROOT,require,read_table,count,totalize
from instruction_tree import read_record,Trees
from native import build_native
from native_addresses import build_addresses
from check_native import literal_check
from register_check import compile_fragment
from verify_tree import equivalent_increment_cfg
from verify_ics import verify,smoke
from reduce import reduce


def check_addresses(candidate):
    record=json.loads(candidate.read_text())
    require(record.get('native_addresses'),'missing address experiment flag')
    require(hashlib.sha256(candidate.with_suffix('.tm').read_bytes()).hexdigest()==record['table_sha256'],'native table hash mismatch')
    tree=read_record(record,candidate.parent);m=build_addresses(record,compile_machine=False)
    arena=Trees();root=arena.import_record(tree,m.registers);arena.install(m,root)
    m.name_sequences();m.generate();m.tm.gc();arena.clear_caches()
    start,edges=read_table(candidate.with_suffix('.tm'))
    require((start,edges)==(m.tm.start,m.tm.states),'address table does not rebuild exactly')
    require(count(edges)==record['raw_states']==record['final_states']==len(reduce(totalize(start,edges))),'address state count mismatch')
    reference=build_native(record)
    a=compile_fragment(reference,reference.find_seq('main().0'),terminal='return')
    b=compile_fragment(m,m.find_seq('main().0'),terminal='return')
    return {'states':count(edges),'matched_cfg_segment_pairs':equivalent_increment_cfg(a,b),
            'smoke':smoke(start,edges,1000000),'literal_ir':literal_check(m,checks=1024),
            'status':'experimental; computational checks only'}


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--candidate',type=Path,default=ROOT/'scratch/native-native.json')
    args=p.parse_args();record=json.loads(args.candidate.read_text())
    report=check_addresses(args.candidate) if record.get('native_addresses') else verify(args.candidate)
    print(json.dumps(report,indent=2))
