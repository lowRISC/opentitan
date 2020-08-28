# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from enum import IntEnum
import sys
from typing import Dict

from riscvmodel.types import Immediate  # type: ignore

from shared.insn_yaml import Insn, load_insns_yaml

from .model import OTBNModel


# Load the insns.yml file at module load time: we'll use its data while
# declaring the classes. The point is that an OTBNInsn below is an instance of
# a particular Insn object from shared.insn_yaml, so we want a class variable
# on the OTBNInsn that points at the corresponding Insn.
try:
    _INSNS_FILE = load_insns_yaml()
except RuntimeError as err:
    sys.stderr.write('{}\n'.format(err))
    sys.exit(1)


class DummyInsn(Insn):
    '''A dummy instruction that will never be decoded. Used for the insn class
    variable in the OTBNInsn base class.

    '''
    def __init__(self) -> None:
        fake_yml = {
            'mnemonic': 'dummy-insn',
            'operands': []
        }
        super().__init__(fake_yml, None)


def insn_for_mnemonic(mnemonic: str, num_operands: int) -> Insn:
    '''Look up the named instruction in the loaded YAML data.

    As a sanity check, make sure it has the expected number of operands. If we
    fail to find the right instruction, print a message to stderr and exit
    (rather than raising a RuntimeError: this happens on module load time, so
    it's a lot clearer to the user what's going on this way).

    '''
    insn = _INSNS_FILE.mnemonic_to_insn.get(mnemonic)
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
    insn = DummyInsn()  # type: Insn

    def __init__(self, op_vals: Dict[str, int]):
        self.op_vals = op_vals

    def execute(self, model: OTBNModel) -> None:
        raise NotImplementedError('OTBNInsn.execute')

    def disassemble(self, pc: int) -> str:
        '''Generate an assembly listing for this instruction'''
        return self.insn.disassemble(self.op_vals, 12)


class RV32RegReg(OTBNInsn):
    '''A general class for register-register insns from the RV32I ISA'''
    def __init__(self, op_vals: Dict[str, int]):
        super().__init__(op_vals)
        self.grd = op_vals['grd']
        self.grs1 = op_vals['grs1']
        self.grs2 = op_vals['grs2']


class RV32RegImm(OTBNInsn):
    '''A general class for register-immediate insns from the RV32I ISA'''
    def __init__(self, op_vals: Dict[str, int]):
        super().__init__(op_vals)
        self.grd = op_vals['grd']
        self.grs1 = op_vals['grs1']
        self.imm = op_vals['imm']


class RV32ImmShift(OTBNInsn):
    '''A general class for immediate shift insns from the RV32I ISA'''
    def __init__(self, op_vals: Dict[str, int]):
        super().__init__(op_vals)
        self.grd = op_vals['grd']
        self.grs1 = op_vals['grs1']
        self.shamt = op_vals['shamt']


class ShiftType(IntEnum):
    LSL = 0  # logical shift left
    LSR = 1  # logical shift right


def ShiftReg(reg: int, shift_type: int, shift_bytes: Immediate) -> int:
    assert 0 <= int(shift_bytes)
    shift_bits = int(shift_bytes << 3)

    return (reg << shift_bits
            if shift_type == ShiftType.LSL
            else reg >> shift_bits)
