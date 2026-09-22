"""Small independent interpreter for the builder's binary structured instruction IR.

This models register instructions and relative IP jumps, not the tape backend.
It is useful for differential testing of local arithmetic/constructor changes.
"""
from functools import lru_cache


def compile_fragment(machine, fragment):
    def tree(value):
        if isinstance(value, int):
            return node(value)
        if isinstance(value, (list, tuple)):
            entries = [tree(x) for x in value if x != () and x != []]
            if not entries:
                return None
            result = entries[-1]
            for entry in reversed(entries[:-1]):
                result = (entry, result)
            return result
        return value

    @lru_cache(None)
    def node(index):
        return tree(machine.sequences[index].seq)

    root = (tree(fragment), 'halt')
    leaves = {}
    def visit(value, path):
        if isinstance(value, tuple):
            visit(value[0], path + (0,));visit(value[1], path + (1,))
        else:
            leaves[path] = value
    visit(root, ())

    def lookup(prefix):
        value = root
        path = ()
        while isinstance(value, tuple):
            bit = prefix[len(path)] if len(path) < len(prefix) else 0
            path += (bit,)
            value = value[bit]
        return path

    def jump(path, kind, level):
        positions = [i for i, bit in enumerate(path) if bit == (kind == 'continue')]
        if kind == 'break':
            if len(positions) <= level:
                raise ValueError('fragment jumps beyond its caller')
            i = positions[-1-level]
            return lookup(path[:i] + (1,))
        if level == 0:
            return path
        if len(positions) < level:
            raise ValueError('fragment continue jumps beyond its caller')
        return lookup(path[:positions[-level]])

    cfg = {}
    for path, op in leaves.items():
        if op == 'halt':
            cfg[path] = ('halt',)
        elif op.startswith('_'):
            kind, level = op[1:].split('.')
            cfg[path] = ('goto', jump(path, kind, int(level)))
        else:
            _, register, operation = op.split('.')
            normal = jump(path, 'break', 0)
            cfg[path] = (operation, register, normal,
                         jump(path, 'break', 1) if operation == 'decnz' else normal)
    return lookup(()), cfg


def execute(compiled, registers=None, limit=10_000_000):
    pc, cfg = compiled
    regs = dict(registers or {})
    for step in range(limit):
        op = cfg[pc]
        if op[0] == 'halt':
            return regs, step
        if op[0] == 'goto':
            pc = op[1]
        elif op[0] == 'inc':
            regs[op[1]] = regs.get(op[1], 0) + 1
            pc = op[2]
        elif op[0] == 'decnz':
            value = regs.get(op[1], 0)
            if value:
                regs[op[1]] = value - 1
                pc = op[2]
            else:
                pc = op[3]
        else:
            raise ValueError(op)
    raise RuntimeError(f'fragment exceeded {limit} register steps')


if __name__ == '__main__':
    from machines import ZF2
    from ics import ICS
    for a in range(10):
        for b in range(10):
            m = ZF2();code = compile_fragment(m, m.pair(m.scratch1,m.param1,m.param2))
            regs, _ = execute(code, {'param1':a,'param2':b})
            assert regs.get('scratch1',0) == a + (a+b)*(a+b+1)//2
            assert regs.get('param1',0) == regs.get('param2',0) == 0
            m = ICS();code = compile_fragment(m, m.safety(m.param1,m.param3))
            regs, _ = execute(code, {'param1':a,'param3':b})
            assert regs.get('param1',0) == a+(a==b) and regs.get('param3',0) == b
            assert all(regs.get(f'scratch{i}',0)==0 for i in (1,2,3))
    print('100 pair and 100 safety cases passed')
