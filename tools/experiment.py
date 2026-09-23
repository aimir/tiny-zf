"""Replay a recorded ICS search from its exact initial configuration and seed."""
import argparse
import json
from pathlib import Path
import subprocess
import sys
from machines import ROOT


def replay_native(run,args,directory,initial):
    """Native experiments use the same pinned source, with explicit dependencies."""
    output=directory/'result.json'
    command=[sys.executable,'-B']
    if run['search']=='native-placement':
        frontiers=[]
        for parent in run['frontiers_from_runs']:
            replay=[sys.executable,'-B',str(Path(__file__).resolve()),parent]
            if args.generations is not None:replay+=['--generations',str(args.generations)]
            subprocess.run(replay,check=True)
            frontiers.append(str(ROOT/'scratch'/('replay-'+parent)/'result.frontier.json'))
        command+=[str(ROOT/'tools/place_native.py'),*frontiers,'--width',str(run['placement_width'])]
    elif run['search']=='native-probe':
        command+=[str(ROOT/'tools/probe_native.py'),run['mode'],'--initial',str(initial)]
        command+=['--generations',str(min(args.generations,run['generations']) if args.generations else run['generations'])]
    else:
        command+=[str(ROOT/'tools/search_native.py'),'--initial',str(initial)]
        for name in ('seed','grid','width','batch','tree_candidates','tree_batch','tree_width','tree_screen','memory_mb'):
            command+=['--'+name.replace('_','-'),str(run[name])]
        command+=['--generations',str(args.generations or run['generations'])]
        command+=['--tree-generations',str(min(args.generations,run['tree_generations']) if args.generations else run['tree_generations'])]
        for name in ('configured_pools','require_native','distinct_sources'):
            if run.get(name):command+=['--'+name.replace('_','-')]
        if run.get('initial_population'):
            base=json.loads(initial.read_text())
            tree=json.loads(Path(base['instruction_tree']).read_text())
            population=[{'record':base,'tree':tree}]+[{'record':r} for r in run['initial_population']]
            frontier=directory/'initial.frontier.json';frontier.write_text(json.dumps(population)+'\n')
            command+=['--resume-frontier',str(frontier)]
    command+=['--output',str(output)]
    subprocess.run(command,check=True)
    if args.generations is None:
        result=json.loads(output.read_text())
        if result['final_states']!=run['final_states']:raise ValueError('native experiment differs from recorded count')
        if run.get('table_sha256') and result['table_sha256']!=run['table_sha256']:raise ValueError('native experiment table hash differs')
    print('Result:',output)


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('id',help='experiment ID from a reference/*-experiments.json manifest')
    p.add_argument('--workers',type=int,help='override the recorded/default worker count')
    p.add_argument('--generations',type=int,help='optional shorter exploratory run')
    args=p.parse_args()
    data=json.loads((ROOT/'reference/ics-experiments.json').read_text())
    for name in ('backend-experiments.json', 'combined-experiments.json', 'pairing-experiments.json', 'decoder-experiments.json', 'native-experiments.json'):
        manifest=ROOT/'reference'/name
        if manifest.exists():
            extra=json.loads(manifest.read_text())
            data['runs']+=[{'initial':extra.get('initial'),**r} for r in extra['runs']]
    matches=[r for r in data['runs'] if r['id']==args.id]
    if len(matches)!=1 or (args.workers is not None and args.workers<1):
        p.error('unknown experiment or invalid worker count')
    run=matches[0]
    workers=args.workers or run.get('workers',4)
    if args.generations is not None and args.generations<1:p.error('generations must be positive')
    directory=ROOT/'scratch'/('replay-'+args.id)
    directory.mkdir(parents=True,exist_ok=True)
    initial=directory/'initial.json'
    initial_record=run.get('initial')
    if 'initial_from_run' in run:
        parent=run['initial_from_run']
        replay=[sys.executable,'-B',str(Path(__file__).resolve()),parent]
        if args.workers is not None:replay+=['--workers',str(args.workers)]
        if args.generations is not None:replay+=['--generations',str(args.generations)]
        subprocess.run(replay,check=True)
        parent_file=ROOT/'scratch'/('replay-'+parent)/'result.json'
        initial_record=json.loads(parent_file.read_text())
        if initial_record.get('instruction_tree'):
            initial_record['instruction_tree']=str(parent_file.parent/initial_record['instruction_tree'])
    if run.get('initial_tree'):
        initial_record={**initial_record, 'instruction_tree':str(ROOT/'reference'/run['initial_tree'])}
    initial.write_text(json.dumps(initial_record,indent=2)+'\n')
    if run['search'].startswith('native'):
        replay_native(run,args,directory,initial)
        return
    script={'order':'search_ics.py','joint':'search_joint.py','operators':'search_operators.py','grammar':'search_grammar.py','grammar-probe':'search_grammar.py','rewrites':'search_rewrites.py','tree':'search_tree.py','combined':'search_combined.py','pairing':'search_pairing.py','decoder':'search_decoder.py'}[run['search']]
    output=directory/'result.json'
    command=[sys.executable,'-B',str(ROOT/'tools'/script),'--initial',str(initial),
             '--output',str(output)]
    if run['search'] not in ('tree','pairing','decoder'):command+=['--workers',str(workers)]
    if run.get('resume_frontier'):
        command+=['--initial-frontier',str(parent_file.with_suffix('.frontier.json'))]
    if run['search']=='grammar-probe':
        command+=['--probe-grid']
    elif run['search']=='operators':
        command+=['--mask',str(run['payload_mask'])]
    else:
        for name in ('seed','width','batch'):
            command+=['--'+name,str(run[name])]
        command+=['--generations',str(args.generations or run['generations'])]
        if run['search'] in ('pairing','decoder'):
            for name in ('tree_candidates','tree_batch','tree_width','tree_screen','memory_mb'):
                command+=['--'+name.replace('_','-'),str(run[name])]
            command+=['--tree-generations',str(min(args.generations,run['tree_generations']) if args.generations else run['tree_generations'])]
            if run.get('dual'):command+=['--dual']
            if run.get('packed_counter'):command+=['--packed-counter']
            if run.get('borrow_stack'):command+=['--borrow-stack']
        if run['search']=='combined':
            for name in ('shortlist','screen_slack','tree_rounds','tree_batch','tree_width','tree_keep',
                         'deep_rounds','deep_count','mode','memory_mb'):
                command+=['--'+name.replace('_','-'),str(run[name])]
            command+=['--exploration-slots',str(run.get('exploration_slots',0))]
            if run.get('parent_donors'):command+=['--parent-donors']
            if run.get('edge_rewrites'):command+=['--edge-rewrites']
        if run['search']=='tree':
            command+=['--mode',run['mode'],'--break-floor',str(run['break_floor']),'--screen',str(run['screen'])]
            if not run.get('commute'):command+=['--no-commute']
            if run.get('stratified'):command+=['--stratified']
            if run.get('edge_rewrites'):command+=['--edge-rewrites']
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
