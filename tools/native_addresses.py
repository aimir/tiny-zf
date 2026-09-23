"""Expose register selectors to instruction-tree search; audit their state flow."""
from functools import lru_cache
from machines import require
from native import build_native,NativeRegisters
from instruction_tree import Trees


def resolve_addresses(machine,compiled):
    start,cfg=compiled;todo=[(start,0)];out={};names=list(machine.registers)
    while todo:
        key=todo.pop()
        if key in out:continue
        pc,selected=key;op=cfg[pc]
        if op[0]=='goto':new=('goto',(op[1],selected))
        elif op[0] in ('return','halt'):
            require(selected==0,'live register selection at exit');new=op
        elif op[0]=='tape':
            kind=op[1]
            if kind=='sel':
                require(selected<len(names),'native selector overruns register file')
                new=('goto',(op[2],selected+1))
            else:
                require(0<selected<=len(names),'native operation lacks selection')
                name=names[selected-1]
                require(kind in ('inc','decnz'),'address experiment currently supports inc/decnz only')
                new=(kind,name,(op[2],0),(op[3],0))
        else:
            require(selected==0,'mixed abstract/native selection state');new=(*op[:2],*((x,0) for x in op[2:]))
        out[key]=new
        if new[0]=='goto':todo.append(new[1])
        elif new[0] not in ('return','halt'):todo.extend(new[2:])
    return (start,0),out


def expose(arena,root,names):
    @lru_cache(None)
    def address(index,kind):
        return arena.node('1.sel',address(index-1,kind) if index else '1.'+kind)
    @lru_cache(None)
    def visit(v):
        if isinstance(v,str):
            if v.startswith('3.'):
                _,name,kind=v.split('.')
                require(kind in ('inc','decnz'),'address experiment requires ordinary operations')
                return address(names.index(name),kind)
            return v
        a,b=arena.nodes[v];return arena.node(visit(a),visit(b))
    return visit(root)


def build_addresses(record,*,compile_machine=True):
    require(not (record.get('native') or {}).get('moves'),'native moves not supported by this address experiment')
    machine=build_native(record,compile_machine=compile_machine)
    machine.native_addresses=True
    machine.registers=NativeRegisters(machine.registers);machine.registers.native_addresses=True
    if compile_machine:
        arena=Trees();root=arena.import_machine(machine);root=expose(arena,root,list(machine.registers))
        arena.install(machine,root);machine.name_sequences();machine.generate();machine.tm.gc();arena.clear_caches()
    return machine
