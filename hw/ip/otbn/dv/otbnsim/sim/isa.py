# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import sys
from typing import Dict, Iterator, Optional, Tuple, Callable

from shared.insn_yaml import Insn, DummyInsn, load_insns_yaml

from .state import OTBNState


# Load the insns.yml file at module load time: we'll use its data while
# declaring the classes. The point is that an OTBNInsn below is an instance of
# a particular Insn object from shared.insn_yaml, so we want a class variable
# on the OTBNInsn that points at the corresponding Insn.
try:
    INSNS_FILE = load_insns_yaml()
except RuntimeError as err:
    sys.stderr.write('{}\n'.format(err))
    sys.exit(1)


def insn_for_mnemonic(mnemonic: str, num_operands: int) -> Insn:
    '''Look up the named instruction in the loaded YAML data.

    To make sure nothing's gone really wrong, make sure it has the expected
    number of operands. If we fail to find the right instruction, print a
    message to stderr and exit (rather than raising a RuntimeError: this
    happens on module load time, so it's a lot clearer to the user what's going
    on this way).

    '''
    insn = INSNS_FILE.mnemonic_to_insn.get(mnemonic)
    if insn is None:
        sys.stderr.write('Failed to find an instruction for mnemonic {!r} in '
                         'insns.yml.\n'
                         .format(mnemonic))
        sys.exit(1)

    if len(insn.operands) != num_operands:
        sys.stderr.write('The instruction for mnemonic {!r} in insns.yml has '
                         '{} operands, but we expected {}.\n'
                         .format(mnemonic, len(insn.operands), num_operands))
        sys.exit(1)

    return insn


class OTBNInsn:
    '''A decoded OTBN instruction.

    '''

    # A class variable that holds the Insn subclass corresponding to this
    # instruction.
    insn: Insn = DummyInsn()

    # A class variable that is set by Insn subclasses that represent
    # instructions that affect control flow (and are not allowed at the end of
    # a loop).
    affects_control = False

    # A class variable that is true if this instruction has valid bits. (Set to
    # false by the EmptyInsn subclass)
    has_bits = True

    # A class variable that is true if there will be a cycle of fetch stall
    # after the instruction executes.
    has_fetch_stall = False

    def __init__(self, raw: int, op_vals: Dict[str, int]):
        self.raw = raw
        self.op_vals = op_vals

        # Memoized disassembly for this instruction. We store the PC at which
        # we disassembled too (which should be the same next time around, but
        # it can't hurt to check).
        self._disasm: Optional[Tuple[int, str]] = None

    def execute(self, state: OTBNState) -> Optional[Iterator[None]]:
        '''Execute the instruction

        This may yield (returning an iterator object) if the instruction has
        stalled the processor and will take multiple cycles.

        '''
        raise NotImplementedError('OTBNInsn.execute')

    def disassemble(self, pc: int) -> str:
        '''Generate an assembly listing for this instruction'''
        if self._disasm is not None:
            old_pc, old_disasm = self._disasm
            assert pc == old_pc
            return old_disasm

        disasm = self.insn.disassemble(pc, self.op_vals)
        self._disasm = (pc, disasm)
        return disasm

    @staticmethod
    def to_2s_complement(value: int) -> int:
        '''Interpret the signed value as a 2's complement u32'''
        assert -(1 << 31) <= value < (1 << 31)
        return (1 << 32) + value if value < 0 else value

    def rtl_trace(self, pc: int) -> str:
        '''Return the RTL trace entry for executing this insn'''
        if self.has_bits:
            return (f'E PC: {pc:#010x}, insn: {self.raw:#010x}\n'
                    f'# @{pc:#010x}: {self.insn.mnemonic}')
        else:
            return (f'E PC: {pc:#010x}, insn: ??\n'
                    f'# @{pc:#010x}: ??')


class RV32RegReg(OTBNInsn):
    '''A general class for register-register insns from the RV32I ISA'''
    def __init__(self, raw: int, op_vals: Dict[str, int]):
        super().__init__(raw, op_vals)
        self.grd = op_vals['grd']
        self.grs1 = op_vals['grs1']
        self.grs2 = op_vals['grs2']


class RV32RegImm(OTBNInsn):
    '''A general class for register-immediate insns from the RV32I ISA'''
    def __init__(self, raw: int, op_vals: Dict[str, int]):
        super().__init__(raw, op_vals)
        self.grd = op_vals['grd']
        self.grs1 = op_vals['grs1']
        self.imm = op_vals['imm']


class RV32ImmShift(OTBNInsn):
    '''A general class for immediate shift insns from the RV32I ISA'''
    def __init__(self, raw: int, op_vals: Dict[str, int]):
        super().__init__(raw, op_vals)
        self.grd = op_vals['grd']
        self.grs1 = op_vals['grs1']
        self.shamt = op_vals['shamt']


class BnVecVecAdd(OTBNInsn):
    '''A general class for vector-vector addition/subtraction insns from the vectorized BN ISA'''
    supported_elens = [32]

    def __init__(self, raw: int, op_vals: Dict[str, int]):
        super().__init__(raw, op_vals)
        self.wrd = op_vals['wrd']
        self.wrs1 = op_vals['wrs1']
        self.wrs2 = op_vals['wrs2']
        self.elen = op_vals['elen']


class BnVecVecTrn(OTBNInsn):
    '''A general class for vector-vector transpose insns from the vectorized BN ISA'''
    supported_elens = [32, 64, 128]

    def __init__(self, raw: int, op_vals: Dict[str, int]):
        super().__init__(raw, op_vals)
        self.wrd = op_vals['wrd']
        self.wrs1 = op_vals['wrs1']
        self.wrs2 = op_vals['wrs2']
        self.elen = op_vals['elen']


class BnVecVecMul(OTBNInsn):
    '''A general class for vector-vector multiplication insns from the vectorized BN ISA'''
    supported_elens = [32]

    def __init__(self, raw: int, op_vals: Dict[str, int]):
        super().__init__(raw, op_vals)
        self.wrd = op_vals['wrd']
        self.wrs1 = op_vals['wrs1']
        self.wrs2 = op_vals['wrs2']
        self.elen = op_vals['elen']


def logical_byte_shift(value: int, shift_type: int, shift_bytes: int) -> int:
    '''Logical shift value by shift_bytes to the left or right.

    value should be an unsigned 256-bit value. shift_type should be 0 (shift
    left) or 1 (shift right), matching the encoding of the big number
    instructions. shift_bytes should be a non-negative number of bytes to shift
    by.

    Returns an unsigned 256-bit value, truncating on an overflowing left shift.
    '''
    mask256 = (1 << 256) - 1
    assert 0 <= value <= mask256
    assert 0 <= shift_type <= 1
    assert 0 <= shift_bytes

    shift_bits = 8 * shift_bytes
    shifted = value << shift_bits if shift_type == 0 else value >> shift_bits
    return shifted & mask256


def shift_vec_elem(value: int, size: int, shift_type: int, shift_bits: int) -> int:
    '''Performs a logical bit shift on an unsigned integer confined to the given bit width.

    With shift_type = 0, the value is shifted left by shift_bits; with shift_type = 1,
    the value is shifted right by shift_bits.

    The resulting shifted value is truncated to size bits.
    '''
    maskSize = (1 << size) - 1
    assert 0 <= value <= maskSize
    assert 0 <= shift_type <= 1
    assert 0 <= shift_bits

    if shift_type == 0:
        result = (value << shift_bits) & maskSize
    else:
        result = (value >> shift_bits) & maskSize

    return result


def extract_vec_elem(value: int, elem: int, size: int) -> int:
    '''Returns the elem-th vector element from a 256-bit vector of size-bit elements interpreted as
    unsigned integer.
    '''
    assert 0 <= value < (1 << 256)
    assert 0 <= elem < (256 // size)
    return (value >> (elem * size)) & ((1 << size) - 1)


def extract_quarter_word(value: int, qwsel: int) -> int:
    '''Extracts a 64-bit quarter word from a 256-bit value.'''
    assert 0 <= qwsel <= 3
    return extract_vec_elem(value, qwsel, 64)


def lower_d_bits(value: int, d: int) -> int:
    '''Extracts the lower d bits of the value.'''
    assert 0 <= d
    assert 0 <= value
    return value & ((1 << d) - 1)


def upper_d_bits(value: int, d: int) -> int:
    '''Extracts the upper d bits of the value and shifts them down by d.'''
    assert 0 <= d
    assert 0 <= value
    return lower_d_bits(value >> d, d)


def element_length_in_bits(elen: int) -> int:
    '''Returns the corresponding bit width for a given ELEN encoding.

    Encoding | ELEN | Size in bits
    0        | .8s  |  32
    1        | .4d  |  64
    2        | .2q  | 128
    '''
    assert 0 <= elen <= 2
    return 32 * (1 << elen)


def map_elems(op: Callable[[int, int], int], size: int, vec_a: int, vec_b: int) -> int:
    '''Applies the operation op to each pair of elements for the given element size.

    The vectors are expected to be 256-bit numbers where `size`-bit elements are extracted from.
    The op function takes two vector elements, performs the desired operation and is expected to
    return a non-negative value.

    The results are concatenated and returned as a 256-bit number.'''
    result = 0
    for elem in range(256 // size):
        elem_a = extract_vec_elem(vec_a, elem, size)
        elem_b = extract_vec_elem(vec_b, elem, size)

        elem_c = op(elem_a, elem_b)
        elem_c = elem_c & ((1 << size) - 1)
        result |= elem_c << (elem * size)
    return result


def montgomery_mul_no_cond_subtraction(a: int, b: int, q: int, mu: int, size: int) -> int:
    '''Performs a Montgomery multiplication but without the final conditional subtraction.

    The inputs a and b are in Montgomery space.
    The result is also in Montgomery space.

    Algorithm (where []_d are the lower d bits, []^d are the higher d bits):
       r = [c + [[c]_d * mu]_d * q]^d
       # Skipped conditional subtraction step:
       # if r >= q:
       #     r -= q
       return r
    '''
    reg_c = a * b
    reg_tmp = lower_d_bits(reg_c, size)
    reg_tmp = lower_d_bits(reg_tmp * mu, size)
    r = upper_d_bits(reg_c + reg_tmp * q, size)
    return r
