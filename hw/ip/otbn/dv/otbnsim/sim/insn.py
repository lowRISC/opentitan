# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from typing import Dict

from .model import OTBNModel
from .isa import (OTBNInsn, RV32RegReg, RV32RegImm, RV32ImmShift,
                  insn_for_mnemonic,
                  ShiftReg)


class ADD(RV32RegReg):
    insn = insn_for_mnemonic('add', 3)

    def execute(self, model: OTBNModel) -> None:
        val1 = model.state.intreg[self.grs1]
        val2 = model.state.intreg[self.grs2]
        model.state.intreg[self.grd] = val1 + val2


class ADDI(RV32RegImm):
    insn = insn_for_mnemonic('addi', 3)

    def execute(self, model: OTBNModel) -> None:
        val1 = model.state.intreg[self.grs1]
        model.state.intreg[self.grd] = val1 + self.imm


class LUI(OTBNInsn):
    insn = insn_for_mnemonic('lui', 2)

    def __init__(self, op_vals: Dict[str, int]):
        super().__init__(op_vals)
        self.grd = op_vals['grd']
        self.imm = op_vals['imm']

    def execute(self, model: OTBNModel) -> None:
        model.state.intreg[self.grd] = (self.imm << 12)


class SUB(RV32RegReg):
    insn = insn_for_mnemonic('sub', 3)

    def execute(self, model: OTBNModel) -> None:
        val1 = model.state.intreg[self.grs1]
        val2 = model.state.intreg[self.grs2]
        model.state.intreg[self.grd] = val1 - val2


class SLL(RV32RegReg):
    insn = insn_for_mnemonic('sll', 3)

    def execute(self, model: OTBNModel) -> None:
        val1 = model.state.intreg[self.grs1]
        val2 = model.state.intreg[self.grs2] & 0x1f
        model.state.intreg[self.grd] = val1 << val2


class SLLI(RV32ImmShift):
    insn = insn_for_mnemonic('slli', 3)

    def execute(self, model: OTBNModel) -> None:
        val1 = model.state.intreg[self.grs1]
        model.state.intreg[self.grd] = val1 << self.shamt


class SRL(RV32RegReg):
    insn = insn_for_mnemonic('srl', 3)

    def execute(self, model: OTBNModel) -> None:
        val1 = model.state.intreg[self.grs1]
        val2 = model.state.intreg[self.grs2] & 0x1f
        model.state.intreg[self.grd] = val1 >> val2


class SRLI(RV32ImmShift):
    insn = insn_for_mnemonic('srli', 3)

    def execute(self, model: OTBNModel) -> None:
        val1 = model.state.intreg[self.grs1]
        model.state.intreg[self.grd] = val1 >> self.shamt


class SRA(RV32RegReg):
    insn = insn_for_mnemonic('sra', 3)

    def execute(self, model: OTBNModel) -> None:
        usrc = model.state.intreg[self.grs1].unsigned()
        shift = model.state.intreg[self.grs2].unsigned() & 0x1f
        if usrc >> 31:
            to_clear = 32 - shift
            sign_mask = (((1 << 32) - 1) >> to_clear) << to_clear
        else:
            sign_mask = 0

        model.state.intreg[self.grd] = sign_mask | (usrc >> shift)


class SRAI(RV32ImmShift):
    insn = insn_for_mnemonic('srai', 3)

    def execute(self, model: OTBNModel) -> None:
        usrc = model.state.intreg[self.grs1].unsigned()
        shift = self.shamt
        if usrc >> 31:
            to_clear = 32 - shift
            sign_mask = (((1 << 32) - 1) >> to_clear) << to_clear
        else:
            sign_mask = 0

        model.state.intreg[self.grd] = sign_mask | (usrc >> shift)


class AND(RV32RegReg):
    insn = insn_for_mnemonic('and', 3)

    def execute(self, model: OTBNModel) -> None:
        val1 = model.state.intreg[self.grs1]
        val2 = model.state.intreg[self.grs2]
        model.state.intreg[self.grd] = val1 & val2


class ANDI(RV32RegImm):
    insn = insn_for_mnemonic('andi', 3)

    def execute(self, model: OTBNModel) -> None:
        val1 = model.state.intreg[self.grs1]
        model.state.intreg[self.grd] = val1 & self.imm


class OR(RV32RegReg):
    insn = insn_for_mnemonic('or', 3)

    def execute(self, model: OTBNModel) -> None:
        val1 = model.state.intreg[self.grs1]
        val2 = model.state.intreg[self.grs2]
        model.state.intreg[self.grd] = val1 | val2


class ORI(RV32RegImm):
    insn = insn_for_mnemonic('ori', 3)

    def execute(self, model: OTBNModel) -> None:
        val1 = model.state.intreg[self.grs1]
        model.state.intreg[self.grd] = val1 | self.imm


class XOR(RV32RegReg):
    insn = insn_for_mnemonic('xor', 3)

    def execute(self, model: OTBNModel) -> None:
        val1 = model.state.intreg[self.grs1]
        val2 = model.state.intreg[self.grs2]
        model.state.intreg[self.grd] = val1 | val2


class XORI(RV32RegImm):
    insn = insn_for_mnemonic('xori', 3)

    def execute(self, model: OTBNModel) -> None:
        val1 = model.state.intreg[self.grs1]
        model.state.intreg[self.grd] = val1 | self.imm


class LW(OTBNInsn):
    insn = insn_for_mnemonic('lw', 3)

    def __init__(self, op_vals: Dict[str, int]):
        super().__init__(op_vals)
        self.grd = op_vals['grd']
        self.offset = op_vals['offset']
        self.grs1 = op_vals['grs1']

    def execute(self, model: OTBNModel) -> None:
        addr = (model.state.intreg[self.grs1] + self.offset).unsigned()
        model.state.intreg[self.grd] = model.state.dmem.load_i32(addr)


class SW(OTBNInsn):
    insn = insn_for_mnemonic('sw', 3)

    def __init__(self, op_vals: Dict[str, int]):
        super().__init__(op_vals)
        self.grs2 = op_vals['grs2']
        self.offset = op_vals['offset']
        self.grs1 = op_vals['grs1']

    def execute(self, model: OTBNModel) -> None:
        addr = (model.state.intreg[self.grs1] + self.offset).unsigned()
        value = int(model.state.intreg[self.grs2])
        model.state.dmem.store_i32(addr, value)


class BEQ(OTBNInsn):
    insn = insn_for_mnemonic('beq', 3)

    def __init__(self, op_vals: Dict[str, int]):
        super().__init__(op_vals)
        self.grs1 = op_vals['grs1']
        self.grs2 = op_vals['grs2']
        self.offset = op_vals['offset']

    def execute(self, model: OTBNModel) -> None:
        val1 = model.state.intreg[self.grs1].value
        val2 = model.state.intreg[self.grs2].value
        if val1 == val2:
            model.state.pc_next = self.offset


class BNE(OTBNInsn):
    insn = insn_for_mnemonic('bne', 3)

    def __init__(self, op_vals: Dict[str, int]):
        super().__init__(op_vals)
        self.grs1 = op_vals['grs1']
        self.grs2 = op_vals['grs2']
        self.offset = op_vals['offset']

    def execute(self, model: OTBNModel) -> None:
        val1 = model.state.intreg[self.grs1].value
        val2 = model.state.intreg[self.grs2].value
        if val1 != val2:
            model.state.pc_next = self.offset


class JAL(OTBNInsn):
    insn = insn_for_mnemonic('jal', 2)

    def __init__(self, op_vals: Dict[str, int]):
        super().__init__(op_vals)
        self.grd = op_vals['grd']
        self.offset = op_vals['offset']

    def execute(self, model: OTBNModel) -> None:
        model.state.intreg[self.grd] = model.state.pc + 4
        model.state.pc_next = self.offset


class JALR(OTBNInsn):
    insn = insn_for_mnemonic('jalr', 3)

    def __init__(self, op_vals: Dict[str, int]):
        super().__init__(op_vals)
        self.grd = op_vals['grd']
        self.grs1 = op_vals['grs1']
        self.offset = op_vals['offset']

    def execute(self, model: OTBNModel) -> None:
        model.state.intreg[self.grd] = model.state.pc + 4
        model.state.pc_next = model.state.intreg[self.grs1] + self.offset


class CSRRS(OTBNInsn):
    insn = insn_for_mnemonic('csrrs', 3)

    def __init__(self, op_vals: Dict[str, int]):
        super().__init__(op_vals)
        self.grd = op_vals['grd']
        self.csr = op_vals['csr']
        self.grs = op_vals['grs']

    def execute(self, model: OTBNModel) -> None:
        raise NotImplementedError('csrrs.execute')


class CSRRW(OTBNInsn):
    insn = insn_for_mnemonic('csrrw', 3)

    def __init__(self, op_vals: Dict[str, int]):
        super().__init__(op_vals)
        self.grd = op_vals['grd']
        self.csr = op_vals['csr']
        self.grs = op_vals['grs']

    def execute(self, model: OTBNModel) -> None:
        raise NotImplementedError('csrrw.execute')


class ECALL(OTBNInsn):
    insn = insn_for_mnemonic('ecall', 0)

    def __init__(self, op_vals: Dict[str, int]):
        super().__init__(op_vals)
        pass

    def execute(self, model: OTBNModel) -> None:
        # INTR_STATE is the interrupt state register. Bit 0 (which is being
        # set) is the 'done' flag.
        model.state.ext_regs.set_bits('INTR_STATE', 1 << 0)
        # STATUS is a status register. Bit 0 (being cleared) is the 'busy' flag
        model.state.ext_regs.clear_bits('STATUS', 1 << 0)

        # As well as the external register, clear an internal 'running' flag to
        # tell the simulation to stop.
        model.state.running = False


class LOOP(OTBNInsn):
    insn = insn_for_mnemonic('loop', 2)

    def __init__(self, op_vals: Dict[str, int]):
        super().__init__(op_vals)
        self.grs = op_vals['grs']
        self.bodysize = op_vals['bodysize']

    def execute(self, model: OTBNModel) -> None:
        num_iters = model.state.intreg[self.grs].unsigned()
        model.state.loop_start(num_iters, self.bodysize)


class LOOPI(OTBNInsn):
    insn = insn_for_mnemonic('loopi', 2)

    def __init__(self, op_vals: Dict[str, int]):
        super().__init__(op_vals)
        self.iterations = op_vals['iterations']
        self.bodysize = op_vals['bodysize']

    def execute(self, model: OTBNModel) -> None:
        model.state.loop_start(self.iterations, self.bodysize)


class BNADD(OTBNInsn):
    insn = insn_for_mnemonic('bn.add', 6)

    def __init__(self, op_vals: Dict[str, int]):
        super().__init__(op_vals)
        self.wrd = op_vals['wrd']
        self.wrs1 = op_vals['wrs1']
        self.wrs2 = op_vals['wrs2']
        self.shift_type = op_vals['shift_type']
        self.shift_bytes = op_vals['shift_bytes']
        self.flag_group = op_vals['flag_group']

    def execute(self, model: OTBNModel) -> None:
        a = int(model.state.wreg[self.wrs1].unsigned())
        b_shifted = ShiftReg(int(model.state.wreg[self.wrs2].unsigned()),
                             self.shift_type, self.shift_bytes)
        (result, flags) = model.add_with_carry(a, b_shifted, 0)
        model.state.wreg[self.wrd] = result
        model.state.flags[self.flag_group] = flags


class BNADDC(OTBNInsn):
    insn = insn_for_mnemonic('bn.addc', 6)

    def __init__(self, op_vals: Dict[str, int]):
        super().__init__(op_vals)
        self.wrd = op_vals['wrd']
        self.wrs1 = op_vals['wrs1']
        self.wrs2 = op_vals['wrs2']
        self.shift_type = op_vals['shift_type']
        self.shift_bytes = op_vals['shift_bytes']
        self.flag_group = op_vals['flag_group']

    def execute(self, model: OTBNModel) -> None:
        a = int(model.state.wreg[self.wrs1].unsigned())
        b_shifted = ShiftReg(int(model.state.wreg[self.wrs2].unsigned()),
                             self.shift_type, self.shift_bytes)
        flag_c = model.state.flags[self.flag_group].C
        (result, flags) = model.add_with_carry(a, b_shifted, flag_c)
        model.state.wreg[self.wrd] = result
        model.state.flags[self.flag_group] = flags


class BNADDI(OTBNInsn):
    insn = insn_for_mnemonic('bn.addi', 4)

    def __init__(self, op_vals: Dict[str, int]):
        super().__init__(op_vals)
        self.wrd = op_vals['wrd']
        self.wrs = op_vals['wrs']
        self.imm = op_vals['imm']
        self.flag_group = op_vals['flag_group']

    def execute(self, model: OTBNModel) -> None:
        a = int(model.state.wreg[self.wrs].unsigned())
        b = int(self.imm)
        (result, flags) = model.add_with_carry(a, b, 0)
        model.state.wreg[self.wrd] = result
        model.state.flags[self.flag_group] = flags


class BNADDM(OTBNInsn):
    insn = insn_for_mnemonic('bn.addm', 3)

    def __init__(self, op_vals: Dict[str, int]):
        super().__init__(op_vals)
        self.wrd = op_vals['wrd']
        self.wrs1 = op_vals['wrs1']
        self.wrs2 = op_vals['wrs2']

    def execute(self, model: OTBNModel) -> None:
        a = int(model.state.wreg[self.wrs1].unsigned())
        b = int(model.state.wreg[self.wrs2].unsigned())
        (result, _) = model.add_with_carry(a, b, 0)
        if result >= int(model.state.mod):
            result -= int(model.state.mod)
        model.state.wreg[self.wrd] = result


class BNMULQACC(OTBNInsn):
    insn = insn_for_mnemonic('bn.mulqacc', 6)

    def __init__(self, op_vals: Dict[str, int]):
        super().__init__(op_vals)
        self.zero_acc = op_vals['zero_acc']
        self.wrs1 = op_vals['wrs1']
        self.wrs1_qwsel = op_vals['wrs1_qwsel']
        self.wrs2 = op_vals['wrs2']
        self.wrs2_qwsel = op_vals['wrs2_qwsel']
        self.acc_shift_imm = op_vals['acc_shift_imm']

    def execute(self, model: OTBNModel) -> None:
        a_qw = model.get_wr_quarterword(self.wrs1, self.wrs1_qwsel)
        b_qw = model.get_wr_quarterword(self.wrs2, self.wrs2_qwsel)

        mul_res = a_qw * b_qw

        acc = int(model.state.single_regs['acc'])
        if self.zero_acc:
            acc = 0

        acc += (mul_res << self.acc_shift_imm)

        model.state.single_regs['acc'].update(acc)


class BNMULQACCWO(OTBNInsn):
    insn = insn_for_mnemonic('bn.mulqacc.wo', 7)

    def __init__(self, op_vals: Dict[str, int]):
        super().__init__(op_vals)
        self.zero_acc = op_vals['zero_acc']
        self.wrd = op_vals['wrd']
        self.wrs1 = op_vals['wrs1']
        self.wrs1_qwsel = op_vals['wrs1_qwsel']
        self.wrs2 = op_vals['wrs2']
        self.wrs2_qwsel = op_vals['wrs2_qwsel']
        self.acc_shift_imm = op_vals['acc_shift_imm']

    def execute(self, model: OTBNModel) -> None:
        a_qw = model.get_wr_quarterword(self.wrs1, self.wrs1_qwsel)
        b_qw = model.get_wr_quarterword(self.wrs2, self.wrs2_qwsel)

        mul_res = a_qw * b_qw

        acc = int(model.state.single_regs['acc'])
        if self.zero_acc:
            acc = 0

        acc += (mul_res << self.acc_shift_imm)

        model.state.wreg[self.wrd].set(acc)

        model.state.single_regs['acc'].update(acc)


class BNMULQACCSO(OTBNInsn):
    insn = insn_for_mnemonic('bn.mulqacc.so', 8)

    def __init__(self, op_vals: Dict[str, int]):
        super().__init__(op_vals)
        self.zero_acc = op_vals['zero_acc']
        self.wrd = op_vals['wrd']
        self.wrd_hwsel = op_vals['wrd_hwsel']
        self.wrs1 = op_vals['wrs1']
        self.wrs1_qwsel = op_vals['wrs1_qwsel']
        self.wrs2 = op_vals['wrs2']
        self.wrs2_qwsel = op_vals['wrs2_qwsel']
        self.acc_shift_imm = op_vals['acc_shift_imm']

    def execute(self, model: OTBNModel) -> None:
        a_qw = model.get_wr_quarterword(self.wrs1, self.wrs1_qwsel)
        b_qw = model.get_wr_quarterword(self.wrs2, self.wrs2_qwsel)

        mul_res = a_qw * b_qw

        acc = int(model.state.single_regs['acc'])
        if self.zero_acc:
            acc = 0

        acc += (mul_res << self.acc_shift_imm)

        # set_wr_halfword expects 0 in upper 128 bits
        acc_lower = acc & ((1 << 128) - 1)
        model.set_wr_halfword(self.wrd, acc_lower, self.wrd_hwsel)
        acc = acc >> 128

        model.state.single_regs['acc'].update(acc)


class BNSUB(OTBNInsn):
    insn = insn_for_mnemonic('bn.sub', 6)

    def __init__(self, op_vals: Dict[str, int]):
        super().__init__(op_vals)
        self.wrd = op_vals['wrd']
        self.wrs1 = op_vals['wrs1']
        self.wrs2 = op_vals['wrs2']
        self.shift_type = op_vals['shift_type']
        self.shift_bytes = op_vals['shift_bytes']
        self.flag_group = op_vals['flag_group']

    def execute(self, model: OTBNModel) -> None:
        a = int(model.state.wreg[self.wrs1])
        b_shifted = ShiftReg(int(model.state.wreg[self.wrs2]), self.shift_type,
                             self.shift_bytes)
        (result, flags) = model.add_with_carry(a, -b_shifted, 0)
        model.state.wreg[self.wrd] = result
        model.state.flags[self.flag_group] = flags


class BNSUBB(OTBNInsn):
    insn = insn_for_mnemonic('bn.subb', 6)

    def __init__(self, op_vals: Dict[str, int]):
        super().__init__(op_vals)
        self.wrd = op_vals['wrd']
        self.wrs1 = op_vals['wrs1']
        self.wrs2 = op_vals['wrs2']
        self.shift_type = op_vals['shift_type']
        self.shift_bytes = op_vals['shift_bytes']
        self.flag_group = op_vals['flag_group']

    def execute(self, model: OTBNModel) -> None:
        a = int(model.state.wreg[self.wrs1])
        b_shifted = ShiftReg(int(model.state.wreg[self.wrs2]), self.shift_type,
                             self.shift_bytes)
        (result,
         flags) = model.add_with_carry(a, -b_shifted,
                                       1 - model.state.flags[self.flag_group].C)
        model.state.wreg[self.wrd] = result
        model.state.flags[self.flag_group] = flags


class BNSUBI(OTBNInsn):
    insn = insn_for_mnemonic('bn.subi', 4)

    def __init__(self, op_vals: Dict[str, int]):
        super().__init__(op_vals)
        self.wrd = op_vals['wrd']
        self.wrs = op_vals['wrs']
        self.imm = op_vals['imm']
        self.flag_group = op_vals['flag_group']

    def execute(self, model: OTBNModel) -> None:
        a = int(model.state.wreg[self.wrs])
        b = int(self.imm)
        (result, flags) = model.add_with_carry(a, -b, 0)
        model.state.wreg[self.wrd] = result
        model.state.flags[self.flag_group] = flags


class BNSUBM(OTBNInsn):
    insn = insn_for_mnemonic('bn.subm', 3)

    def __init__(self, op_vals: Dict[str, int]):
        super().__init__(op_vals)
        self.wrd = op_vals['wrd']
        self.wrs1 = op_vals['wrs1']
        self.wrs2 = op_vals['wrs2']

    def execute(self, model: OTBNModel) -> None:
        a = int(model.state.wreg[self.wrs1])
        b = int(model.state.wreg[self.wrs2])
        result, _ = model.add_with_carry(a, -b, 0)
        if result < 0:
            result += model.state.mod
        model.state.wreg[self.wrd] = result


class BNAND(OTBNInsn):
    insn = insn_for_mnemonic('bn.and', 5)

    def __init__(self, op_vals: Dict[str, int]):
        super().__init__(op_vals)
        self.wrd = op_vals['wrd']
        self.wrs1 = op_vals['wrs1']
        self.wrs2 = op_vals['wrs2']
        self.shift_type = op_vals['shift_type']
        self.shift_bytes = op_vals['shift_bytes']

    def execute(self, model: OTBNModel) -> None:
        b_shifted = ShiftReg(model.state.wreg[self.wrs2],
                             self.shift_type, self.shift_bytes)
        a = model.state.wreg[self.wrs1]
        model.state.wreg[self.wrd] = a & b_shifted


class BNOR(OTBNInsn):
    insn = insn_for_mnemonic('bn.or', 5)

    def __init__(self, op_vals: Dict[str, int]):
        super().__init__(op_vals)
        self.wrd = op_vals['wrd']
        self.wrs1 = op_vals['wrs1']
        self.wrs2 = op_vals['wrs2']
        self.shift_type = op_vals['shift_type']
        self.shift_bytes = op_vals['shift_bytes']

    def execute(self, model: OTBNModel) -> None:
        b_shifted = ShiftReg(model.state.wreg[self.wrs2],
                             self.shift_type, self.shift_bytes)
        a = model.state.wreg[self.wrs1]
        model.state.wreg[self.wrd] = a | b_shifted


class BNNOT(OTBNInsn):
    insn = insn_for_mnemonic('bn.not', 4)

    def __init__(self, op_vals: Dict[str, int]):
        super().__init__(op_vals)
        self.wrd = op_vals['wrd']
        self.wrs = op_vals['wrs']
        self.shift_type = op_vals['shift_type']
        self.shift_bytes = op_vals['shift_bytes']

    def execute(self, model: OTBNModel) -> None:
        b_shifted = ShiftReg(model.state.wreg[self.wrs],
                             self.shift_type, self.shift_bytes)
        model.state.wreg[self.wrd] = ~b_shifted


class BNXOR(OTBNInsn):
    insn = insn_for_mnemonic('bn.xor', 5)

    def __init__(self, op_vals: Dict[str, int]):
        super().__init__(op_vals)
        self.wrd = op_vals['wrd']
        self.wrs1 = op_vals['wrs1']
        self.wrs2 = op_vals['wrs2']
        self.shift_type = op_vals['shift_type']
        self.shift_bytes = op_vals['shift_bytes']

    def execute(self, model: OTBNModel) -> None:
        b_shifted = ShiftReg(model.state.wreg[self.wrs2],
                             self.shift_type, self.shift_bytes)
        a = model.state.wreg[self.wrs1]
        model.state.wreg[self.wrd] = a ^ b_shifted


class BNRSHI(OTBNInsn):
    insn = insn_for_mnemonic('bn.rshi', 4)

    def __init__(self, op_vals: Dict[str, int]):
        super().__init__(op_vals)
        self.wrd = op_vals['wrd']
        self.wrs1 = op_vals['wrs1']
        self.wrs2 = op_vals['wrs2']
        self.imm = op_vals['imm']

    def execute(self, model: OTBNModel) -> None:
        a = int(model.state.wreg[self.wrs1])
        b = int(model.state.wreg[self.wrs2])
        shifted = ((a << 256) | b) >> self.imm
        model.state.wreg[self.wrd] = shifted & ((1 << 256) - 1)


class BNRSEL(OTBNInsn):
    insn = insn_for_mnemonic('bn.sel', 5)

    def __init__(self, op_vals: Dict[str, int]):
        super().__init__(op_vals)
        self.wrd = op_vals['wrd']
        self.wrs1 = op_vals['wrs1']
        self.wrs2 = op_vals['wrs2']
        self.flag_group = op_vals['flag_group']
        self.flag = op_vals['flag']

    def execute(self, model: OTBNModel) -> None:
        flag_is_set = model.state.flags[self.flag_group].get_by_idx(self.flag)
        val = model.state.wreg[self.wrs1 if flag_is_set else self.wrs2]
        model.state.wreg[self.wrd] = val


class BNCMP(OTBNInsn):
    insn = insn_for_mnemonic('bn.cmp', 5)

    def __init__(self, op_vals: Dict[str, int]):
        super().__init__(op_vals)
        self.wrs1 = op_vals['wrs1']
        self.wrs2 = op_vals['wrs2']
        self.shift_type = op_vals['shift_type']
        self.shift_bytes = op_vals['shift_bytes']
        self.flag_group = op_vals['flag_group']

    def execute(self, model: OTBNModel) -> None:
        a = int(model.state.wreg[self.wrs1])
        b_shifted = ShiftReg(int(model.state.wreg[self.wrs2]), self.shift_type,
                             self.shift_bytes)
        (_, flags) = model.add_with_carry(a, -b_shifted, 0)
        model.state.flags[self.flag_group] = flags


class BNCMPB(OTBNInsn):
    insn = insn_for_mnemonic('bn.cmpb', 5)

    def __init__(self, op_vals: Dict[str, int]):
        super().__init__(op_vals)
        self.wrs1 = op_vals['wrs1']
        self.wrs2 = op_vals['wrs2']
        self.shift_type = op_vals['shift_type']
        self.shift_bytes = op_vals['shift_bytes']
        self.flag_group = op_vals['flag_group']

    def execute(self, model: OTBNModel) -> None:
        a = int(model.state.wreg[self.wrs1])
        b_shifted = ShiftReg(int(model.state.wreg[self.wrs2]), self.shift_type,
                             self.shift_bytes)
        carry_flag = 1 - model.state.flags[self.flag_group].C
        (_, flags) = model.add_with_carry(a, -b_shifted, carry_flag)
        model.state.flags[self.flag_group] = flags


class BNLID(OTBNInsn):
    insn = insn_for_mnemonic('bn.lid', 5)

    def __init__(self, op_vals: Dict[str, int]):
        super().__init__(op_vals)
        self.grd = op_vals['grd']
        self.grd_inc = op_vals['grd_inc']
        self.offset = op_vals['offset']
        self.grs1 = op_vals['grs1']
        self.grs1_inc = op_vals['grs1_inc']

    def execute(self, model: OTBNModel) -> None:
        addr = int(model.state.intreg[self.grs1] + int(self.offset))
        wrd = int(model.state.intreg[self.grd])
        model.state.wreg[wrd] = model.state.dmem.load_i256(addr)

        if self.grd_inc:
            model.state.intreg[self.grd] += 1
        if self.grs1_inc:
            model.state.intreg[self.grs1] += 32


class BNSID(OTBNInsn):
    insn = insn_for_mnemonic('bn.sid', 5)

    def __init__(self, op_vals: Dict[str, int]):
        super().__init__(op_vals)
        self.grs2 = op_vals['grs2']
        self.grs2_inc = op_vals['grs2_inc']
        self.offset = op_vals['offset']
        self.grs1 = op_vals['grs1']
        self.grs1_inc = op_vals['grs1_inc']

    def execute(self, model: OTBNModel) -> None:
        idx = int(model.state.intreg[self.grs2])
        addr = int(model.state.intreg[self.grs1] + int(self.offset))

        wrs = model.state.wreg[idx]
        model.state.dmem.store_i256(addr, int(wrs))

        if self.grs2_inc:
            model.state.intreg[self.grs2] += 1
        if self.grs1_inc:
            model.state.intreg[self.grs1] += 32


class BNMOV(OTBNInsn):
    insn = insn_for_mnemonic('bn.mov', 2)

    def __init__(self, op_vals: Dict[str, int]):
        super().__init__(op_vals)
        self.wrd = op_vals['wrd']
        self.wrs = op_vals['wrs']

    def execute(self, model: OTBNModel) -> None:
        model.state.wreg[self.wrd] = model.state.wreg[self.wrs]


class BNMOVR(OTBNInsn):
    insn = insn_for_mnemonic('bn.movr', 4)

    def __init__(self, op_vals: Dict[str, int]):
        super().__init__(op_vals)
        self.grd = op_vals['grd']
        self.grd_inc = op_vals['grd_inc']
        self.grs = op_vals['grs']
        self.grs_inc = op_vals['grs_inc']

    def execute(self, model: OTBNModel) -> None:
        wrd = int(model.state.intreg[self.grd])
        wrs = int(model.state.intreg[self.grs])
        model.state.wreg[wrd] = model.state.wreg[wrs]

        if self.grd_inc:
            model.state.intreg[self.grd] += 1
        if self.grs_inc:
            model.state.intreg[self.grs] += 1


class BNWSRRS(OTBNInsn):
    insn = insn_for_mnemonic('bn.wsrrs', 3)

    def __init__(self, op_vals: Dict[str, int]):
        super().__init__(op_vals)
        self.wrd = op_vals['wrd']
        self.wsr = op_vals['wsr']
        self.wrs = op_vals['wrs']

    def execute(self, model: OTBNModel) -> None:
        idx = self.wsr
        old_val = model.state.wcsr_read(idx)
        new_val = old_val | model.state.wreg[self.wrs]

        model.state.wreg[self.wrd] = old_val
        model.state.wcsr_write(idx, new_val)


class BNWSRRW(OTBNInsn):
    insn = insn_for_mnemonic('bn.wsrrw', 3)

    def __init__(self, op_vals: Dict[str, int]):
        super().__init__(op_vals)
        self.wrd = op_vals['wrd']
        self.wsr = op_vals['wsr']
        self.wrs = op_vals['wrs']

    def execute(self, model: OTBNModel) -> None:
        idx = self.wsr
        old_val = model.state.wcsr_read(idx)
        new_val = model.state.wreg[self.wrs]

        model.state.wreg[self.wrd] = old_val
        model.state.wcsr_write(idx, new_val)


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
    BNWSRRS, BNWSRRW
]
