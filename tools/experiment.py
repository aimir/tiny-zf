"""Replay a recorded ICS search from its exact initial configuration and seed."""
import argparse
import json
from pathlib import Path
import subprocess
import sys
from machines import ROOT


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('id',help='experiment ID from reference/ics-experiments.json')
    p.add_argument('--workers',type=int,default=4)
    p.add_argument('--generations',type=int,help='optional shorter exploratory run')
    args=p.parse_args()
    data=json.loads((ROOT/'reference/ics-experiments.json').read_text())
    matches=[r for r in data['runs'] if r['id']==args.id]
    if len(matches)!=1 or args.workers<1:
        p.error('unknown experiment or invalid worker count')
    run=matches[0]
    directory=ROOT/'scratch'/('replay-'+args.id)
    directory.mkdir(parents=True,exist_ok=True)
    initial=directory/'initial.json'
    initial.write_text(json.dumps(run['initial'],indent=2)+'\n')
    script={'order':'search_ics.py','joint':'search_joint.py','operators':'search_operators.py','grammar':'search_grammar.py','grammar-probe':'search_grammar.py','rewrites':'search_rewrites.py'}[run['search']]
    output=directory/'result.json'
    command=[sys.executable,'-B',str(ROOT/'tools'/script),'--initial',str(initial),
             '--workers',str(args.workers),'--output',str(output)]
    if run['search']=='grammar-probe':
        command+=['--probe-grid']
    elif run['search']=='operators':
        command+=['--mask',str(run['payload_mask'])]
    else:
        for name in ('seed','width','batch'):
            command+=['--'+name,str(run[name])]
        command+=['--generations',str(args.generations or run['generations'])]
        if run.get('shared_operations') and run['search']=='joint':
            command+=['--sharing']
        if run.get('preserve_main') and run['search']=='grammar':
            command+=['--preserve-main']
        if run.get('storage_search'):
            command+=['--storage']
        if run.get('encoding_search'):
            command+=['--encoding']
    subprocess.run(command,check=True)
    if args.generations is None:
        result=json.loads(output.read_text())
        if result['final_states']!=run['final_states']:
            raise ValueError('search result differs from recorded count')
    print('Result:',output)


if __name__=='__main__':
    main()
