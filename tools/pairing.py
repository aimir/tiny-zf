"""Experimental arithmetic kernels. These change the encoding, not the logic.

Dyadic pairing D(a,b) = 2**b * (2*a+1) - 1 preserves the distinguished
formula codes 0 and 1. Every ordinary pair/unpair call is replaced together.
The three registers must be distinct. Outputs start at zero; input registers
are consumed. No other register is read or written.
"""
from machines import ZF2  # Initializes the pinned compiler import path.
from TMBuilder import subroutine


class Dyadic:
    @subroutine
    def pair(self, out, in1, in2):
        return self.pair_body(out, in1, in2)

    def pair_body(self, out, in1, in2):
        assert len({out, in1, in2}) == 3
        return [self.while_decnz(in1, [out.inc, out.inc]),
                self.while_decnz(in2, [
                    self.while_decnz(out, [in1.inc, in1.inc]),
                    in1.inc,
                    self.while_decnz(in1, out.inc)])]

    @subroutine
    def unpair(self, out1, out2, in1):
        return self.unpair_body(out1, out2, in1)

    def unpair_body(self, out1, out2, in1):
        assert len({out1, out2, in1}) == 3
        return [self.label('loop', [in1.decnz, [
            [in1.decnz, [out1.inc, 'continue_loop']],
            [out2.inc, [self.while_decnz(out1, in1.inc), 'continue_loop']]]])]


class DyadicPositive(Dyadic):
    def pair_body(self, out, in1, in2):
        assert len({out, in1, in2}) == 3
        return [self.while_decnz(in1, [out.inc, out.inc]), out.inc,
                self.while_decnz(in2, [
                    self.while_decnz(out, [in1.inc, in1.inc]),
                    self.while_decnz(in1, out.inc)]),
                self.label('done', [[out.decnz, 'break_done'], 'break_done'])]


class DyadicAlternating(Dyadic):
    """Alternate doubling buffers, copying only at the final odd iteration."""
    def pair_body(self, out, in1, in2):
        assert len({out, in1, in2}) == 3
        return [self.label('loop', [
            self.while_decnz(in1, [out.inc, out.inc]),
            [in2.decnz, [
                self.while_decnz(out, [in1.inc, in1.inc]),
                [in1.inc, [
                    [in2.decnz, [out.inc, 'continue_loop']],
                    self.while_decnz(in1, out.inc)]]]]])]


class DyadicPositiveInverse:
    @subroutine
    def unpair(self, out1, out2, in1):
        return self.unpair_body(out1, out2, in1)

    def unpair_body(self, out1, out2, in1):
        assert len({out1, out2, in1}) == 3
        return [in1.inc, self.label('outer', [
            self.label('half', [in1.decnz, [
                [in1.decnz, [out1.inc, 'continue_half']], 'break_outer']]),
            [out2.inc, [self.while_decnz(out1, in1.inc), 'continue_outer']]])]


class DyadicTags:
    """D(payload,k) via fixed doublings, with no tag counter."""
    @subroutine
    def tag(self, k):
        return self.fixed_tag(self.topwff, k)

    @subroutine
    def binary(self, k):
        if not self.binary_mode:
            return [self.cons(), self.tag(k)]
        a, b = ((self.topwff, self.scratch1) if self.reverse_pairing_payload
                else (self.scratch1, self.topwff))
        return [self.unpair(self.scratch1, self.scratch2, self.wffstack),
                self.while_decnz(self.scratch2, self.wffstack.inc),
                self.pair(self.scratch2, a, b), self.fixed_tag(self.scratch2, k)]

    @subroutine
    def fixed_tag(self, source, k):
        target = self.scratch2 if source == self.topwff else self.topwff
        result = []
        for i in range(k+1):
            result.append(self.while_decnz(source, [target.inc, target.inc]))
            if i:
                result.append(target.inc)
            source, target = target, source
        if source != self.topwff:
            result.append(self.while_decnz(source, self.topwff.inc))
        return result


class DyadicRepeatedTags(DyadicTags):
    @subroutine
    def fixed_tag(self, source, k):
        scratch = getattr(self, self.tag_scratch)
        if source == self.topwff:
            result = [self.while_decnz(source, [scratch.inc, scratch.inc]),
                      self.while_decnz(scratch, self.topwff.inc)]
        else:
            result = [self.while_decnz(source, [self.topwff.inc, self.topwff.inc])]
        body = [self.while_decnz(self.topwff, [scratch.inc, scratch.inc]),
                scratch.inc, self.while_decnz(scratch, self.topwff.inc)]
        return [result, *([body]*k)]


class DualDyadic:
    """Use E(a,b)=D(b,a) for stacks, proof fields and inner formula payloads."""
    @subroutine
    def pair(self, out, in1, in2):
        return self.pair_body(out, in2, in1)

    @subroutine
    def unpair(self, out1, out2, in1):
        return self.unpair_body(out2, out1, in1)


class DualGenericTags(DyadicTags):
    """Outer formula tags still use D(payload,k), preserving codes 0 and 1."""
    @subroutine
    def tag(self, k):
        if self.tag_mode == 0:
            return [[self.scratch2.inc]*k,
                    self.while_decnz(self.topwff,self.scratch1.inc),
                    self.pair(self.topwff,self.scratch2,self.scratch1)]
        if self.tag_mode == 1:
            return [[self.scratch1.inc]*k,
                    self.pair(self.scratch2,self.scratch1,self.topwff),
                    self.while_decnz(self.scratch2,self.topwff.inc)]
        if self.tag_mode == 2:
            return [[self.scratch2.inc]*k,
                    self.pair(self.scratch1,self.scratch2,self.topwff),
                    self.while_decnz(self.scratch1,self.topwff.inc)]
        return [[self.scratch1.inc]*k,
                self.while_decnz(self.topwff,self.scratch2.inc),
                self.pair(self.topwff,self.scratch1,self.scratch2)]

    @subroutine
    def binary(self, k):
        if not self.binary_mode:return [self.cons(),self.tag(k)]
        a,b=((self.topwff,self.scratch1) if self.reverse_pairing_payload
             else (self.scratch1,self.topwff))
        return [self.unpair(self.scratch1,self.scratch2,self.wffstack),
                self.while_decnz(self.scratch2,self.wffstack.inc),
                self.pair(self.scratch2,a,b),[self.scratch1.inc]*k,
                self.pair(self.topwff,self.scratch1,self.scratch2)]


KERNELS = {'dyadic': Dyadic, 'dyadic-positive': DyadicPositive,
           'dyadic-alternating': DyadicAlternating}


class Retag:
    @subroutine
    def wim(self):
        return self.binary(self.tag_order[0])

    @subroutine
    def wn(self):
        return self.tag(self.tag_order[1])

    @subroutine
    def wal(self):
        return self.binary(self.tag_order[2])


def build_pairing(record, kernel=None, *, tags=None, positive_inverse=None,
                  tag_order=None, dual=None,
                  compile_machine=True):
    from joint import build_joint, decode
    options = record.get('pairing', {})
    kernel = kernel if kernel is not None else options.get('kernel', 'dyadic')
    tags = tags if tags is not None else options.get('tags', 'generic')
    positive_inverse = (positive_inverse if positive_inverse is not None
                        else options.get('positive_inverse', False))
    tag_order = tuple(tag_order if tag_order is not None else options.get('tag_order', (2,3,4)))
    dual = dual if dual is not None else options.get('dual', False)
    if sorted(tag_order) != [2,3,4]:
        raise ValueError('tag order must permute implication, negation, forall')
    # This experiment always uses explicit tagged constructors. The legacy -1
    # lowering has no binary/tag interface; interpret that mutation as mode 0.
    if record.get('fusion', -1) < 0:
        record = {**record, 'fusion': 0}
    machine = build_joint(decode(record), sharing=record.get('shared_operations', False),
                          grammar=record.get('grammar'),
                          formula_choices=record.get('formula_choices'),
                          compile_machine=False)
    cls = KERNELS[kernel]
    machine.__class__ = type('PairingICS', (cls, type(machine)), {})
    if positive_inverse:
        machine.__class__ = type('PositiveInverseICS', (DyadicPositiveInverse, type(machine)), {})
    if dual:
        machine.__class__ = type('DualPairingICS', (DualDyadic, type(machine)), {})
        if tags == 'generic':
            machine.__class__ = type('DualTaggedICS', (DualGenericTags, type(machine)), {})
    if tags != 'generic':
        cls = DyadicTags if tags == 'alternating' else DyadicRepeatedTags
        if tags not in ('alternating', 'repeat1', 'repeat2'):
            raise ValueError('unknown fixed-tag lowering')
        machine.__class__ = type('TaggedPairingICS', (cls, type(machine)), {})
        machine.tag_scratch = 'scratch1' if tags == 'repeat1' else 'scratch2'
    machine.reverse_pairing_payload = record.get('reverse_payload', False)
    machine.__class__ = type('RetaggedICS', (Retag, type(machine)), {})
    machine.tag_order = tag_order
    if compile_machine:
        machine.build_machine()
    return machine
