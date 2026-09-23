"""Experimental adjacent-register tape transfers and register placement."""
from machines import require
import tm

# Normalize the selection marker by shifting its prefix, then move the source
# value into the register immediately to its right by relocating their separator.
MOVE_RIGHT = '''
1.movr 0 1 R 1.movr.gap
1.movr.gap 0 0 R 1.movr.gap
1.movr.gap 1 0 R 1.movr.prefix
1.movr.prefix 1 1 R 1.movr.prefix
1.movr.prefix 0 1 R 1.movr.separator
1.movr.separator 1 0 R 1.movr.prefix
1.movr.separator 0 0 R 1.movr.first
1.movr.first 1 1 R 1.movr.second
1.movr.second 0 0 L 2.ret1
1.movr.second 1 0 R 1.movr.join
1.movr.join 1 1 R 1.movr.join
1.movr.join 0 1 L 2.ret1
'''


# Normalize and fill the selector, joining into the left neighbor. Splitting
# before the last source one also handles zero inputs. That split bit is always
# one (the filled separator for zero inputs), so reuse the existing 1.sel/1 edge.
MOVE_LEFT = """
1.movl 0 1 R 1.movl.gap
1.movl.gap 0 0 R 1.movl.gap
1.movl.gap 1 0 R 1.movl.prefix
1.movl.prefix 1 1 R 1.movl.prefix
1.movl.prefix 0 1 R 1.movl.separator
1.movl.separator 1 0 R 1.movl.prefix
1.movl.separator 0 1 R 1.movl.end
1.movl.end 1 1 R 1.movl.end
1.movl.end 0 0 L 1.movl.last
1.movl.last 1 1 L 1.sel
"""



class NativeRegisters(dict):
    pass


class NativeTransfers:
    def while_decnz(self, var, body):
        if isinstance(body,str) and body.endswith('.inc'):
            target=body.split('.')[1]
            if [str(var),target] in self.native_options.get('moves',[]):
                return [self.native_opcodes[(str(var),target)]]
        return super().while_decnz(var,body)

    def generate(self):
        super().generate()
        for text in (MOVE_RIGHT,MOVE_LEFT):
            for line in text.splitlines():self.tm.loadline(line,'<native transfer>',0)
        registers=list(self.registers)
        for kind in ('movr','movl'):
            sources=[a for (a,b),op in self.native_opcodes.items() if op.endswith('.'+kind)]
            if sources:
                for i,name in enumerate(registers[:max(registers.index(a) for a in sources)+1]):
                    self.tm.states[(f'3.{name}.{kind}','0')]=tm.Transition('0','R','1.sel')
                    self.tm.states[(f'3.{name}.{kind}','1')]=tm.Transition('1','R',f'3.{registers[i-1]}.{kind}' if i else '1.'+kind)


def apply_native(machine,options):
    order=options.get('register_order',list(machine.registers))
    require(sorted(order)==sorted(machine.registers),'native register order is not a permutation')
    require(order[-1]=='scratch3','unused scratch must remain outside the active register prefix')
    pairs=options.get('moves',[])
    require(len(set(tuple(p) for p in pairs))==len(pairs),'duplicate native transfer')
    for a,b in pairs:
        require(a in order and b in order and abs(order.index(a)-order.index(b))==1,'native transfer registers are not adjacent')
    machine.tm=tm.TuringMachine();machine.registers={};machine.nextreg=0;machine.prevreg=None
    for name in order:setattr(machine,name,machine.reg(name))
    machine.native_opcodes={(a,b):f'3.{a}.'+('movr' if order.index(a)>order.index(b) else 'movl') for a,b in pairs}
    machine.registers=NativeRegisters(machine.registers)
    machine.registers.native_primitives=set(machine.native_opcodes.values())
    machine.native_options=options
    machine.native_expansions={machine.native_opcodes[a,b]:(f'3.{a}.decnz',(f'3.{b}.inc','_continue.2')) for a,b in pairs}
    machine.__class__=type('NativeICS',(NativeTransfers,type(machine)),{})
    return machine


def build_native(record, *, compile_machine=True):
    from joint import build_joint,decode
    return build_joint(decode(record),sharing=record.get('shared_operations',False),
                       grammar=record.get('grammar'),formula_choices=record.get('formula_choices'),
                       decoder=record.get('decoder'),native=record.get('native'),
                       compile_machine=compile_machine)
