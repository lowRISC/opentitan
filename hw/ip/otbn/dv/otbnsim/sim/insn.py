# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from typing import Dict

from .alert import LoopError
from .flags import FlagReg
from .isa import (DecodeError, OTBNInsn, RV32RegReg, RV32RegImm, RV32ImmShift,
                  insn_for_mnemonic, logical_byte_shift)
from .state import OTBNState


class ADD(RV32RegReg):
    insn = insn_for_mnemonic('add', 3)

    def execute(self, state: OTBNState) -> None:
        val1 = state.gprs.get_reg(self.grs1).read_unsigned()
        val2 = state.gprs.get_reg(self.grs2).read_unsigned()
        result = (val1 + val2) & ((1 << 32) - 1)
        state.gprs.get_reg(self.grd).write_unsigned(result)


class ADDI(RV32RegImm):
    insn = insn_for_mnemonic('addi', 3)

    def execute(self, state: OTBNState) -> None:
        val1 = state.gprs.get_reg(self.grs1).read_unsigned()
        result = (val1 + self.imm) & ((1 << 32) - 1)
        state.gprs.get_reg(self.grd).write_unsigned(result)


class LUI(OTBNInsn):
    insn = insn_for_mnemonic('lui', 2)

    def __init__(self, raw: int, op_vals: Dict[str, int]):
        super().__init__(raw, op_vals)
        self.grd = op_vals['grd']
        self.imm = op_vals['imm']

    def execute(self, state: OTBNState) -> None:
        state.gprs.get_reg(self.grd).write_unsigned(self.imm << 12)


class SUB(RV32RegReg):
    insn = insn_for_mnemonic('sub', 3)

    def execute(self, state: OTBNState) -> None:
        val1 = state.gprs.get_reg(self.grs1).read_unsigned()
        val2 = state.gprs.get_reg(self.grs2).read_unsigned()
        result = (val1 - val2) & ((1 << 32) - 1)
        state.gprs.get_reg(self.grd).write_unsigned(result)


class SLL(RV32RegReg):
    insn = insn_for_mnemonic('sll', 3)

    def execute(self, state: OTBNState) -> None:
        val1 = state.gprs.get_reg(self.grs1).read_unsigned()
        val2 = state.gprs.get_reg(self.grs2).read_unsigned() & 0x1f
        result = (val1 << val2) & ((1 << 32) - 1)
        state.gprs.get_reg(self.grd).write_unsigned(result)


class SLLI(RV32ImmShift):
    insn = insn_for_mnemonic('slli', 3)

    def execute(self, state: OTBNState) -> None:
        val1 = state.gprs.get_reg(self.grs1).read_unsigned()
        result = (val1 << self.shamt) & ((1 << 32) - 1)
        state.gprs.get_reg(self.grd).write_unsigned(result)


class SRL(RV32RegReg):
    insn = insn_for_mnemonic('srl', 3)

    def execute(self, state: OTBNState) -> None:
        val1 = state.gprs.get_reg(self.grs1).read_unsigned()
        val2 = state.gprs.get_reg(self.grs2).read_unsigned() & 0x1f
        result = val1 >> val2
        state.gprs.get_reg(self.grd).write_unsigned(result)


class SRLI(RV32ImmShift):
    insn = insn_for_mnemonic('srli', 3)

    def execute(self, state: OTBNState) -> None:
        val1 = state.gprs.get_reg(self.grs1).read_unsigned()
        result = val1 >> self.shamt
        state.gprs.get_reg(self.grd).write_unsigned(result)


class SRA(RV32RegReg):
    insn = insn_for_mnemonic('sra', 3)

    def execute(self, state: OTBNState) -> None:
        val1 = state.gprs.get_reg(self.grs1).read_signed()
        val2 = state.gprs.get_reg(self.grs2).read_unsigned() & 0x1f
        result = val1 >> val2
        state.gprs.get_reg(self.grd).write_signed(result)


class SRAI(RV32ImmShift):
    insn = insn_for_mnemonic('srai', 3)

    def execute(self, state: OTBNState) -> None:
        val1 = state.gprs.get_reg(self.grs1).read_signed()
        val2 = self.shamt
        result = val1 >> val2
        state.gprs.get_reg(self.grd).write_signed(result)


class AND(RV32RegReg):
    insn = insn_for_mnemonic('and', 3)

    def execute(self, state: OTBNState) -> None:
        val1 = state.gprs.get_reg(self.grs1).read_unsigned()
        val2 = state.gprs.get_reg(self.grs2).read_unsigned()
        result = val1 & val2
        state.gprs.get_reg(self.grd).write_unsigned(result)


class ANDI(RV32RegImm):
    insn = insn_for_mnemonic('andi', 3)

    def execute(self, state: OTBNState) -> None:
        val1 = state.gprs.get_reg(self.grs1).read_unsigned()
        val2 = self.as_u32(self.imm)
        result = val1 & val2
        state.gprs.get_reg(self.grd).write_unsigned(result)


class OR(RV32RegReg):
    insn = insn_for_mnemonic('or', 3)

    def execute(self, state: OTBNState) -> None:
        val1 = state.gprs.get_reg(self.grs1).read_unsigned()
        val2 = state.gprs.get_reg(self.grs2).read_unsigned()
        result = val1 | val2
        state.gprs.get_reg(self.grd).write_unsigned(result)


class ORI(RV32RegImm):
    insn = insn_for_mnemonic('ori', 3)

    def execute(self, state: OTBNState) -> None:
        val1 = state.gprs.get_reg(self.grs1).read_unsigned()
        val2 = self.as_u32(self.imm)
        result = val1 | val2
        state.gprs.get_reg(self.grd).write_unsigned(result)


class XOR(RV32RegReg):
    insn = insn_for_mnemonic('xor', 3)

    def execute(self, state: OTBNState) -> None:
        val1 = state.gprs.get_reg(self.grs1).read_unsigned()
        val2 = state.gprs.get_reg(self.grs2).read_unsigned()
        result = val1 ^ val2
        state.gprs.get_reg(self.grd).write_unsigned(result)


class XORI(RV32RegImm):
    insn = insn_for_mnemonic('xori', 3)

    def execute(self, state: OTBNState) -> None:
        val1 = state.gprs.get_reg(self.grs1).read_unsigned()
        val2 = self.as_u32(self.imm)
        result = val1 ^ val2
        state.gprs.get_reg(self.grd).write_unsigned(result)


class LW(OTBNInsn):
    insn = insn_for_mnemonic('lw', 3)

    def __init__(self, raw: int, op_vals: Dict[str, int]):
        super().__init__(raw, op_vals)
        self.grd = op_vals['grd']
        self.offset = op_vals['offset']
        self.grs1 = op_vals['grs1']

    def execute(self, state: OTBNState) -> None:
        base = state.gprs.get_reg(self.grs1).read_unsigned()
        addr = (base + self.offset) & ((1 << 32) - 1)
        result = state.dmem.load_u32(addr)
        state.gprs.get_reg(self.grd).write_unsigned(result)


class SW(OTBNInsn):
    insn = insn_for_mnemonic('sw', 3)

    def __init__(self, raw: int, op_vals: Dict[str, int]):
        super().__init__(raw, op_vals)
        self.grs2 = op_vals['grs2']
        self.offset = op_vals['offset']
        self.grs1 = op_vals['grs1']

    def execute(self, state: OTBNState) -> None:
        base = state.gprs.get_reg(self.grs1).read_unsigned()
        addr = (base + self.offset) & ((1 << 32) - 1)
        value = state.gprs.get_reg(self.grs2).read_unsigned()
        state.dmem.store_u32(addr, value)


class BEQ(OTBNInsn):
    insn = insn_for_mnemonic('beq', 3)
    affects_control = True

    def __init__(self, raw: int, op_vals: Dict[str, int]):
        super().__init__(raw, op_vals)
        self.grs1 = op_vals['grs1']
        self.grs2 = op_vals['grs2']
        self.offset = op_vals['offset']

    def execute(self, state: OTBNState) -> None:
        val1 = state.gprs.get_reg(self.grs1).read_unsigned()
        val2 = state.gprs.get_reg(self.grs2).read_unsigned()
        if val1 == val2:
            state.pc_next = self.offset


class BNE(OTBNInsn):
    insn = insn_for_mnemonic('bne', 3)
    affects_control = True

    def __init__(self, raw: int, op_vals: Dict[str, int]):
        super().__init__(raw, op_vals)
        self.grs1 = op_vals['grs1']
        self.grs2 = op_vals['grs2']
        self.offset = op_vals['offset']

    def execute(self, state: OTBNState) -> None:
        val1 = state.gprs.get_reg(self.grs1).read_unsigned()
        val2 = state.gprs.get_reg(self.grs2).read_unsigned()
        if val1 != val2:
            state.pc_next = self.offset


class JAL(OTBNInsn):
    insn = insn_for_mnemonic('jal', 2)
    affects_control = True

    def __init__(self, raw: int, op_vals: Dict[str, int]):
        super().__init__(raw, op_vals)
        self.grd = op_vals['grd']
        self.offset = op_vals['offset']

    def execute(self, state: OTBNState) -> None:
        link_pc = (state.pc + 4) & ((1 << 32) - 1)
        state.gprs.get_reg(self.grd).write_unsigned(link_pc)
        state.pc_next = self.offset


class JALR(OTBNInsn):
    insn = insn_for_mnemonic('jalr', 3)
    affects_control = True

    def __init__(self, raw: int, op_vals: Dict[str, int]):
        super().__init__(raw, op_vals)
        self.grd = op_vals['grd']
        self.grs1 = op_vals['grs1']
        self.offset = op_vals['offset']

    def execute(self, state: OTBNState) -> None:
        val1 = state.gprs.get_reg(self.grs1).read_unsigned()
        link_pc = (state.pc + 4) & ((1 << 32) - 1)

        state.gprs.get_reg(self.grd).write_unsigned(link_pc)
        state.pc_next = (val1 + self.offset) & ((1 << 32) - 1)


class CSRRS(OTBNInsn):
    insn = insn_for_mnemonic('csrrs', 3)

    def __init__(self, raw: int, op_vals: Dict[str, int]):
        super().__init__(raw, op_vals)
        self.grd = op_vals['grd']
        self.csr = op_vals['csr']
        self.grs1 = op_vals['grs1']

    def execute(self, state: OTBNState) -> None:
        old_val = state.read_csr(self.csr)
        bits_to_set = state.gprs.get_reg(self.grs1).read_unsigned()
        new_val = old_val | bits_to_set

        state.gprs.get_reg(self.grd).write_unsigned(old_val)
        state.write_csr(self.csr, new_val)


class CSRRW(OTBNInsn):
    insn = insn_for_mnemonic('csrrw', 3)

    def __init__(self, raw: int, op_vals: Dict[str, int]):
        super().__init__(raw, op_vals)
        self.grd = op_vals['grd']
        self.csr = op_vals['csr']
        self.grs1 = op_vals['grs1']

    def execute(self, state: OTBNState) -> None:
        new_val = state.gprs.get_reg(self.grs1).read_unsigned()

        if self.grd != 0:
            old_val = state.read_csr(self.csr)
            state.gprs.get_reg(self.grd).write_unsigned(old_val)

        state.write_csr(self.csr, new_val)


class ECALL(OTBNInsn):
    insn = insn_for_mnemonic('ecall', 0)

    def __init__(self, raw: int, op_vals: Dict[str, int]):
        super().__init__(raw, op_vals)
        pass

    def execute(self, state: OTBNState) -> None:
        # Set INTR_STATE.done and STATUS, reflecting the fact we've stopped.
        state.stop(None)


class LOOP(OTBNInsn):
    insn = insn_for_mnemonic('loop', 2)
    affects_control = True

    def __init__(self, raw: int, op_vals: Dict[str, int]):
        super().__init__(raw, op_vals)
        self.grs = op_vals['grs']
        self.bodysize = op_vals['bodysize']

    def execute(self, state: OTBNState) -> None:
        num_iters = state.gprs.get_reg(self.grs).read_unsigned()
        if num_iters == 0:
            raise LoopError('loop count in x{} was zero'
                            .format(self.grs))

        state.loop_start(num_iters, self.bodysize)


class LOOPI(OTBNInsn):
    insn = insn_for_mnemonic('loopi', 2)
    affects_control = True

    def __init__(self, raw: int, op_vals: Dict[str, int]):
        super().__init__(raw, op_vals)
        self.iterations = op_vals['iterations']
        self.bodysize = op_vals['bodysize']

    def execute(self, state: OTBNState) -> None:
        state.loop_start(self.iterations, self.bodysize)


class BNADD(OTBNInsn):
    insn = insn_for_mnemonic('bn.add', 6)

    def __init__(self, raw: int, op_vals: Dict[str, int]):
        super().__init__(raw, op_vals)
        self.wrd = op_vals['wrd']
        self.wrs1 = op_vals['wrs1']
        self.wrs2 = op_vals['wrs2']
        self.shift_type = op_vals['shift_type']
        self.shift_bytes = op_vals['shift_bits'] // 8
        self.flag_group = op_vals['flag_group']

    def execute(self, state: OTBNState) -> None:
        a = state.wdrs.get_reg(self.wrs1).read_unsigned()
        b = state.wdrs.get_reg(self.wrs2).read_unsigned()
        b_shifted = logical_byte_shift(b, self.shift_type, self.shift_bytes)

        (result, flags) = state.add_with_carry(a, b_shifted, 0)
        state.wdrs.get_reg(self.wrd).write_unsigned(result)
        state.set_flags(self.flag_group, flags)


class BNADDC(OTBNInsn):
    insn = insn_for_mnemonic('bn.addc', 6)

    def __init__(self, raw: int, op_vals: Dict[str, int]):
        super().__init__(raw, op_vals)
        self.wrd = op_vals['wrd']
        self.wrs1 = op_vals['wrs1']
        self.wrs2 = op_vals['wrs2']
        self.shift_type = op_vals['shift_type']
        self.shift_bytes = op_vals['shift_bits'] // 8
        self.flag_group = op_vals['flag_group']

    def execute(self, state: OTBNState) -> None:
        a = state.wdrs.get_reg(self.wrs1).read_unsigned()
        b = state.wdrs.get_reg(self.wrs2).read_unsigned()
        b_shifted = logical_byte_shift(b, self.shift_type, self.shift_bytes)

        carry = int(state.csrs.flags[self.flag_group].C)
        (result, flags) = state.add_with_carry(a, b_shifted, carry)
        state.wdrs.get_reg(self.wrd).write_unsigned(result)
        state.set_flags(self.flag_group, flags)


class BNADDI(OTBNInsn):
    insn = insn_for_mnemonic('bn.addi', 4)

    def __init__(self, raw: int, op_vals: Dict[str, int]):
        super().__init__(raw, op_vals)
        self.wrd = op_vals['wrd']
        self.wrs = op_vals['wrs']
        self.imm = op_vals['imm']
        self.flag_group = op_vals['flag_group']

    def execute(self, state: OTBNState) -> None:
        a = state.wdrs.get_reg(self.wrs).read_unsigned()
        b = self.imm

        (result, flags) = state.add_with_carry(a, b, 0)
        state.wdrs.get_reg(self.wrd).write_unsigned(result)
        state.set_flags(self.flag_group, flags)


class BNADDM(OTBNInsn):
    insn = insn_for_mnemonic('bn.addm', 3)

    def __init__(self, raw: int, op_vals: Dict[str, int]):
        super().__init__(raw, op_vals)
        self.wrd = op_vals['wrd']
        self.wrs1 = op_vals['wrs1']
        self.wrs2 = op_vals['wrs2']

    def execute(self, state: OTBNState) -> None:
        a = state.wdrs.get_reg(self.wrs1).read_unsigned()
        b = state.wdrs.get_reg(self.wrs2).read_unsigned()
        result = a + b

        mod_val = state.wsrs.MOD.read_unsigned()
        if result >= mod_val:
            result -= mod_val

        result = result & ((1 << 256) - 1)
        state.wdrs.get_reg(self.wrd).write_unsigned(result)


class BNMULQACC(OTBNInsn):
    insn = insn_for_mnemonic('bn.mulqacc', 6)

    def __init__(self, raw: int, op_vals: Dict[str, int]):
        super().__init__(raw, op_vals)
        self.zero_acc = op_vals['zero_acc']
        self.wrs1 = op_vals['wrs1']
        self.wrs1_qwsel = op_vals['wrs1_qwsel']
        self.wrs2 = op_vals['wrs2']
        self.wrs2_qwsel = op_vals['wrs2_qwsel']
        self.acc_shift_imm = op_vals['acc_shift_imm']

    def execute(self, state: OTBNState) -> None:
        a_qw = state.get_quarter_word_unsigned(self.wrs1, self.wrs1_qwsel)
        b_qw = state.get_quarter_word_unsigned(self.wrs2, self.wrs2_qwsel)

        mul_res = a_qw * b_qw

        acc = state.wsrs.ACC.read_unsigned()
        if self.zero_acc:
            acc = 0

        acc += (mul_res << self.acc_shift_imm)

        truncated = acc & ((1 << 256) - 1)
        state.wsrs.ACC.write_unsigned(truncated)


class BNMULQACCWO(OTBNInsn):
    insn = insn_for_mnemonic('bn.mulqacc.wo', 8)

    def __init__(self, raw: int, op_vals: Dict[str, int]):
        super().__init__(raw, op_vals)
        self.zero_acc = op_vals['zero_acc']
        self.wrd = op_vals['wrd']
        self.wrs1 = op_vals['wrs1']
        self.wrs1_qwsel = op_vals['wrs1_qwsel']
        self.wrs2 = op_vals['wrs2']
        self.wrs2_qwsel = op_vals['wrs2_qwsel']
        self.acc_shift_imm = op_vals['acc_shift_imm']
        self.flag_group = op_vals['flag_group']

    def execute(self, state: OTBNState) -> None:
        a_qw = state.get_quarter_word_unsigned(self.wrs1, self.wrs1_qwsel)
        b_qw = state.get_quarter_word_unsigned(self.wrs2, self.wrs2_qwsel)

        mul_res = a_qw * b_qw

        acc = state.wsrs.ACC.read_unsigned()
        if self.zero_acc:
            acc = 0

        acc += (mul_res << self.acc_shift_imm)

        truncated = acc & ((1 << 256) - 1)
        state.wdrs.get_reg(self.wrd).write_unsigned(truncated)
        state.wsrs.ACC.write_unsigned(truncated)
        state.set_mlz_flags(self.flag_group, truncated)


class BNMULQACCSO(OTBNInsn):
    insn = insn_for_mnemonic('bn.mulqacc.so', 9)

    def __init__(self, raw: int, op_vals: Dict[str, int]):
        super().__init__(raw, op_vals)
        self.zero_acc = op_vals['zero_acc']
        self.wrd = op_vals['wrd']
        self.wrd_hwsel = op_vals['wrd_hwsel']
        self.wrs1 = op_vals['wrs1']
        self.wrs1_qwsel = op_vals['wrs1_qwsel']
        self.wrs2 = op_vals['wrs2']
        self.wrs2_qwsel = op_vals['wrs2_qwsel']
        self.acc_shift_imm = op_vals['acc_shift_imm']
        self.flag_group = op_vals['flag_group']

    def execute(self, state: OTBNState) -> None:
        a_qw = state.get_quarter_word_unsigned(self.wrs1, self.wrs1_qwsel)
        b_qw = state.get_quarter_word_unsigned(self.wrs2, self.wrs2_qwsel)

        mul_res = a_qw * b_qw

        acc = state.wsrs.ACC.read_unsigned()
        if self.zero_acc:
            acc = 0

        acc += (mul_res << self.acc_shift_imm)
        truncated = acc & ((1 << 256) - 1)

        lo_part = truncated & ((1 << 128) - 1)
        hi_part = truncated >> 128

        state.set_half_word_unsigned(self.wrd, self.wrd_hwsel, lo_part)
        state.wsrs.ACC.write_unsigned(hi_part)

        old_flags = state.csrs.flags[self.flag_group]
        if self.wrd_hwsel:
            new_flags = FlagReg(C=old_flags.C,
                                M=bool((lo_part >> 127) & 1),
                                L=old_flags.L,
                                Z=old_flags.Z and lo_part == 0)
        else:
            new_flags = FlagReg(C=old_flags.C,
                                M=old_flags.M,
                                L=bool(lo_part & 1),
                                Z=lo_part == 0)
        state.csrs.flags[self.flag_group] = new_flags


class BNSUB(OTBNInsn):
    insn = insn_for_mnemonic('bn.sub', 6)

    def __init__(self, raw: int, op_vals: Dict[str, int]):
        super().__init__(raw, op_vals)
        self.wrd = op_vals['wrd']
        self.wrs1 = op_vals['wrs1']
        self.wrs2 = op_vals['wrs2']
        self.shift_type = op_vals['shift_type']
        self.shift_bytes = op_vals['shift_bits'] // 8
        self.flag_group = op_vals['flag_group']

    def execute(self, state: OTBNState) -> None:
        a = state.wdrs.get_reg(self.wrs1).read_unsigned()
        b = state.wdrs.get_reg(self.wrs2).read_unsigned()
        b_shifted = logical_byte_shift(b, self.shift_type, self.shift_bytes)

        (result, flags) = state.sub_with_borrow(a, b_shifted, 0)
        state.wdrs.get_reg(self.wrd).write_unsigned(result)
        state.set_flags(self.flag_group, flags)


class BNSUBB(OTBNInsn):
    insn = insn_for_mnemonic('bn.subb', 6)

    def __init__(self, raw: int, op_vals: Dict[str, int]):
        super().__init__(raw, op_vals)
        self.wrd = op_vals['wrd']
        self.wrs1 = op_vals['wrs1']
        self.wrs2 = op_vals['wrs2']
        self.shift_type = op_vals['shift_type']
        self.shift_bytes = op_vals['shift_bits'] // 8
        self.flag_group = op_vals['flag_group']

    def execute(self, state: OTBNState) -> None:
        a = state.wdrs.get_reg(self.wrs1).read_unsigned()
        b = state.wdrs.get_reg(self.wrs2).read_unsigned()
        b_shifted = logical_byte_shift(b, self.shift_type, self.shift_bytes)
        borrow = int(state.csrs.flags[self.flag_group].C)

        (result, flags) = state.sub_with_borrow(a, b_shifted, borrow)
        state.wdrs.get_reg(self.wrd).write_unsigned(result)
        state.set_flags(self.flag_group, flags)


class BNSUBI(OTBNInsn):
    insn = insn_for_mnemonic('bn.subi', 4)

    def __init__(self, raw: int, op_vals: Dict[str, int]):
        super().__init__(raw, op_vals)
        self.wrd = op_vals['wrd']
        self.wrs = op_vals['wrs']
        self.imm = op_vals['imm']
        self.flag_group = op_vals['flag_group']

    def execute(self, state: OTBNState) -> None:
        a = state.wdrs.get_reg(self.wrs).read_unsigned()
        b = self.imm

        (result, flags) = state.sub_with_borrow(a, b, 0)
        state.wdrs.get_reg(self.wrd).write_unsigned(result)
        state.set_flags(self.flag_group, flags)


class BNSUBM(OTBNInsn):
    insn = insn_for_mnemonic('bn.subm', 3)

    def __init__(self, raw: int, op_vals: Dict[str, int]):
        super().__init__(raw, op_vals)
        self.wrd = op_vals['wrd']
        self.wrs1 = op_vals['wrs1']
        self.wrs2 = op_vals['wrs2']

    def execute(self, state: OTBNState) -> None:
        a = state.wdrs.get_reg(self.wrs1).read_unsigned()
        b = state.wdrs.get_reg(self.wrs2).read_unsigned()

        mod_val = state.wsrs.MOD.read_unsigned()

        diff = a - b
        if diff < 0:
            diff += mod_val

        result = diff & ((1 << 256) - 1)
        state.wdrs.get_reg(self.wrd).write_unsigned(result)


class BNAND(OTBNInsn):
    insn = insn_for_mnemonic('bn.and', 6)

    def __init__(self, raw: int, op_vals: Dict[str, int]):
        super().__init__(raw, op_vals)
        self.wrd = op_vals['wrd']
        self.wrs1 = op_vals['wrs1']
        self.wrs2 = op_vals['wrs2']
        self.shift_type = op_vals['shift_type']
        self.shift_bytes = op_vals['shift_bits'] // 8
        self.flag_group = op_vals['flag_group']

    def execute(self, state: OTBNState) -> None:
        a = state.wdrs.get_reg(self.wrs1).read_unsigned()
        b = state.wdrs.get_reg(self.wrs2).read_unsigned()
        b_shifted = logical_byte_shift(b, self.shift_type, self.shift_bytes)

        result = a & b_shifted
        state.wdrs.get_reg(self.wrd).write_unsigned(result)
        state.set_mlz_flags(self.flag_group, result)


class BNOR(OTBNInsn):
    insn = insn_for_mnemonic('bn.or', 6)

    def __init__(self, raw: int, op_vals: Dict[str, int]):
        super().__init__(raw, op_vals)
        self.wrd = op_vals['wrd']
        self.wrs1 = op_vals['wrs1']
        self.wrs2 = op_vals['wrs2']
        self.shift_type = op_vals['shift_type']
        self.shift_bytes = op_vals['shift_bits'] // 8
        self.flag_group = op_vals['flag_group']

    def execute(self, state: OTBNState) -> None:
        a = state.wdrs.get_reg(self.wrs1).read_unsigned()
        b = state.wdrs.get_reg(self.wrs2).read_unsigned()
        b_shifted = logical_byte_shift(b, self.shift_type, self.shift_bytes)

        result = a | b_shifted
        state.wdrs.get_reg(self.wrd).write_unsigned(result)
        state.set_mlz_flags(self.flag_group, result)


class BNNOT(OTBNInsn):
    insn = insn_for_mnemonic('bn.not', 5)

    def __init__(self, raw: int, op_vals: Dict[str, int]):
        super().__init__(raw, op_vals)
        self.wrd = op_vals['wrd']
        self.wrs = op_vals['wrs']
        self.shift_type = op_vals['shift_type']
        self.shift_bytes = op_vals['shift_bits'] // 8
        self.flag_group = op_vals['flag_group']

    def execute(self, state: OTBNState) -> None:
        a = state.wdrs.get_reg(self.wrs).read_unsigned()
        a_shifted = logical_byte_shift(a, self.shift_type, self.shift_bytes)

        result = a_shifted ^ ((1 << 256) - 1)
        state.wdrs.get_reg(self.wrd).write_unsigned(result)
        state.set_mlz_flags(self.flag_group, result)


class BNXOR(OTBNInsn):
    insn = insn_for_mnemonic('bn.xor', 6)

    def __init__(self, raw: int, op_vals: Dict[str, int]):
        super().__init__(raw, op_vals)
        self.wrd = op_vals['wrd']
        self.wrs1 = op_vals['wrs1']
        self.wrs2 = op_vals['wrs2']
        self.shift_type = op_vals['shift_type']
        self.shift_bytes = op_vals['shift_bits'] // 8
        self.flag_group = op_vals['flag_group']

    def execute(self, state: OTBNState) -> None:
        a = state.wdrs.get_reg(self.wrs1).read_unsigned()
        b = state.wdrs.get_reg(self.wrs2).read_unsigned()
        b_shifted = logical_byte_shift(b, self.shift_type, self.shift_bytes)

        result = a ^ b_shifted
        state.wdrs.get_reg(self.wrd).write_unsigned(result)
        state.set_mlz_flags(self.flag_group, result)


class BNRSHI(OTBNInsn):
    insn = insn_for_mnemonic('bn.rshi', 4)

    def __init__(self, raw: int, op_vals: Dict[str, int]):
        super().__init__(raw, op_vals)
        self.wrd = op_vals['wrd']
        self.wrs1 = op_vals['wrs1']
        self.wrs2 = op_vals['wrs2']
        self.imm = op_vals['imm']

    def execute(self, state: OTBNState) -> None:
        a = state.wdrs.get_reg(self.wrs1).read_unsigned()
        b = state.wdrs.get_reg(self.wrs2).read_unsigned()

        result = (((a << 256) | b) >> self.imm) & ((1 << 256) - 1)
        state.wdrs.get_reg(self.wrd).write_unsigned(result)


class BNRSEL(OTBNInsn):
    insn = insn_for_mnemonic('bn.sel', 5)

    def __init__(self, raw: int, op_vals: Dict[str, int]):
        super().__init__(raw, op_vals)
        self.wrd = op_vals['wrd']
        self.wrs1 = op_vals['wrs1']
        self.wrs2 = op_vals['wrs2']
        self.flag_group = op_vals['flag_group']
        self.flag = op_vals['flag']

    def execute(self, state: OTBNState) -> None:
        flag_is_set = state.csrs.flags[self.flag_group].get_by_idx(self.flag)
        wrs = self.wrs1 if flag_is_set else self.wrs2
        value = state.wdrs.get_reg(wrs).read_unsigned()
        state.wdrs.get_reg(self.wrd).write_unsigned(value)


class BNCMP(OTBNInsn):
    insn = insn_for_mnemonic('bn.cmp', 5)

    def __init__(self, raw: int, op_vals: Dict[str, int]):
        super().__init__(raw, op_vals)
        self.wrs1 = op_vals['wrs1']
        self.wrs2 = op_vals['wrs2']
        self.shift_type = op_vals['shift_type']
        self.shift_bytes = op_vals['shift_bits'] // 8
        self.flag_group = op_vals['flag_group']

    def execute(self, state: OTBNState) -> None:
        a = state.wdrs.get_reg(self.wrs1).read_unsigned()
        b = state.wdrs.get_reg(self.wrs2).read_unsigned()
        b_shifted = logical_byte_shift(b, self.shift_type, self.shift_bytes)

        (_, flags) = state.sub_with_borrow(a, b_shifted, 0)
        state.set_flags(self.flag_group, flags)


class BNCMPB(OTBNInsn):
    insn = insn_for_mnemonic('bn.cmpb', 5)

    def __init__(self, raw: int, op_vals: Dict[str, int]):
        super().__init__(raw, op_vals)
        self.wrs1 = op_vals['wrs1']
        self.wrs2 = op_vals['wrs2']
        self.shift_type = op_vals['shift_type']
        self.shift_bytes = op_vals['shift_bits'] // 8
        self.flag_group = op_vals['flag_group']

    def execute(self, state: OTBNState) -> None:
        a = state.wdrs.get_reg(self.wrs1).read_unsigned()
        b = state.wdrs.get_reg(self.wrs2).read_unsigned()
        b_shifted = logical_byte_shift(b, self.shift_type, self.shift_bytes)
        borrow = int(state.csrs.flags[self.flag_group].C)

        (_, flags) = state.sub_with_borrow(a, b_shifted, borrow)
        state.set_flags(self.flag_group, flags)


class BNLID(OTBNInsn):
    insn = insn_for_mnemonic('bn.lid', 5)

    def __init__(self, raw: int, op_vals: Dict[str, int]):
        super().__init__(raw, op_vals)
        self.grd = op_vals['grd']
        self.grd_inc = op_vals['grd_inc']
        self.offset = op_vals['offset']
        self.grs1 = op_vals['grs1']
        self.grs1_inc = op_vals['grs1_inc']

        if self.grd_inc and self.grs1_inc:
            raise DecodeError('grd_inc and grs1_inc both set')

    def execute(self, state: OTBNState) -> None:
        grs1_val = state.gprs.get_reg(self.grs1).read_unsigned()
        addr = (grs1_val + self.offset) & ((1 << 32) - 1)
        grd_val = state.gprs.get_reg(self.grd).read_unsigned()

        wrd = grd_val & 0x1f
        value = state.dmem.load_u256(addr)
        state.wdrs.get_reg(wrd).write_unsigned(value)

        if self.grd_inc:
            new_grd_val = (grd_val + 1) & 0x1f
            state.gprs.get_reg(self.grd).write_unsigned(new_grd_val)

        if self.grs1_inc:
            new_grs1_val = (grs1_val + 32) & ((1 << 32) - 1)
            state.gprs.get_reg(self.grs1).write_unsigned(new_grs1_val)


class BNSID(OTBNInsn):
    insn = insn_for_mnemonic('bn.sid', 5)

    def __init__(self, raw: int, op_vals: Dict[str, int]):
        super().__init__(raw, op_vals)
        self.grs2 = op_vals['grs2']
        self.grs2_inc = op_vals['grs2_inc']
        self.offset = op_vals['offset']
        self.grs1 = op_vals['grs1']
        self.grs1_inc = op_vals['grs1_inc']

        if self.grs1_inc and self.grs2_inc:
            raise DecodeError('grs1_inc and grs2_inc both set')

    def execute(self, state: OTBNState) -> None:
        grs1_val = state.gprs.get_reg(self.grs1).read_unsigned()
        addr = (grs1_val + self.offset) & ((1 << 32) - 1)

        grs2_val = state.gprs.get_reg(self.grs2).read_unsigned()
        wrs = grs2_val & 0x1f
        wrs_val = state.wdrs.get_reg(wrs).read_unsigned()

        state.dmem.store_u256(addr, wrs_val)

        if self.grs1_inc:
            new_grs1_val = (grs1_val + 32) & ((1 << 32) - 1)
            state.gprs.get_reg(self.grs1).write_unsigned(new_grs1_val)

        if self.grs2_inc:
            new_grs2_val = (grs2_val + 1) & 0x1f
            state.gprs.get_reg(self.grs2).write_unsigned(new_grs2_val)


class BNMOV(OTBNInsn):
    insn = insn_for_mnemonic('bn.mov', 2)

    def __init__(self, raw: int, op_vals: Dict[str, int]):
        super().__init__(raw, op_vals)
        self.wrd = op_vals['wrd']
        self.wrs = op_vals['wrs']

    def execute(self, state: OTBNState) -> None:
        value = state.wdrs.get_reg(self.wrs).read_unsigned()
        state.wdrs.get_reg(self.wrd).write_unsigned(value)


class BNMOVR(OTBNInsn):
    insn = insn_for_mnemonic('bn.movr', 4)

    def __init__(self, raw: int, op_vals: Dict[str, int]):
        super().__init__(raw, op_vals)
        self.grd = op_vals['grd']
        self.grd_inc = op_vals['grd_inc']
        self.grs = op_vals['grs']
        self.grs_inc = op_vals['grs_inc']

        if self.grd_inc and self.grs_inc:
            raise DecodeError('grd_inc and grs_inc both set')

    def execute(self, state: OTBNState) -> None:
        grd_val = state.gprs.get_reg(self.grd).read_unsigned()
        grs_val = state.gprs.get_reg(self.grs).read_unsigned()

        wrd = grd_val & 0x1f
        wrs = grs_val & 0x1f

        value = state.wdrs.get_reg(wrs).read_unsigned()
        state.wdrs.get_reg(wrd).write_unsigned(value)

        if self.grd_inc:
            new_grd_val = (grd_val + 1) & 0x1f
            state.gprs.get_reg(self.grd).write_unsigned(new_grd_val)

        if self.grs_inc:
            new_grs_val = (grs_val + 1) & 0x1f
            state.gprs.get_reg(self.grs).write_unsigned(new_grs_val)


class BNWSRR(OTBNInsn):
    insn = insn_for_mnemonic('bn.wsrr', 2)

    def __init__(self, raw: int, op_vals: Dict[str, int]):
        super().__init__(raw, op_vals)
        self.wrd = op_vals['wrd']
        self.wsr = op_vals['wsr']

    def execute(self, state: OTBNState) -> None:
        val = state.wsrs.read_at_idx(self.wsr)
        state.wdrs.get_reg(self.wrd).write_unsigned(val)


class BNWSRW(OTBNInsn):
    insn = insn_for_mnemonic('bn.wsrw', 2)

    def __init__(self, raw: int, op_vals: Dict[str, int]):
        super().__init__(raw, op_vals)
        self.wsr = op_vals['wsr']
        self.wrs = op_vals['wrs']

    def execute(self, state: OTBNState) -> None:
        val = state.wdrs.get_reg(self.wrs).read_unsigned()
        state.wsrs.write_at_idx(self.wsr, val)


INSN_CLASSES = [
    ADD, ADDI, LUI, SUB, SLL, SLLI, SRL, SRLI, SRA, SRAI,
    AND, ANDI, OR, ORI, XOR, XORI,
    LW, SW,
    BEQ, BNE, JAL, JALR,
    CSRRS, CSRRW,
    ECALL,
    LOOP, LOOPI,

    BNADD, BNADDC, BNADDI, BNADDM,
    BNMULQACC, BNMULQACCWO, BNMULQACCSO,
    BNSUB, BNSUBB, BNSUBI, BNSUBM,
    BNAND, BNOR, BNNOT, BNXOR,
    BNRSHI,
    BNRSEL,
    BNCMP, BNCMPB,
    BNLID, BNSID,
    BNMOV, BNMOVR,
    BNWSRR, BNWSRW
]
