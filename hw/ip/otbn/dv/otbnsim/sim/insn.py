# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from typing import Dict, Iterator, Optional

from .constants import ErrBits
from .flags import FlagReg
from .isa import (OTBNInsn, RV32RegReg, RV32RegImm,
                  RV32ImmShift, BnVecVecAdd, BnVecVecMul, BnVecVecTrn,
                  insn_for_mnemonic, logical_byte_shift,
                  extract_quarter_word, extract_vec_elem, element_length_in_bits,
                  shift_vec_elem, map_elems, montgomery_mul_no_cond_subtraction)
from .state import OTBNState


class ADD(RV32RegReg):
    insn = insn_for_mnemonic('add', 3)

    def execute(self, state: OTBNState) -> None:
        val1 = state.gprs.get_reg(self.grs1).read_unsigned()
        val2 = state.gprs.get_reg(self.grs2).read_unsigned()
        if state.gprs.call_stack_err:
            state.stop_at_end_of_cycle(ErrBits.CALL_STACK)
            return

        result = (val1 + val2) & ((1 << 32) - 1)
        state.gprs.get_reg(self.grd).write_unsigned(result)


class ADDI(RV32RegImm):
    insn = insn_for_mnemonic('addi', 3)

    def execute(self, state: OTBNState) -> None:
        val1 = state.gprs.get_reg(self.grs1).read_unsigned()
        if state.gprs.call_stack_err:
            state.stop_at_end_of_cycle(ErrBits.CALL_STACK)
            return

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
        if state.gprs.call_stack_err:
            state.stop_at_end_of_cycle(ErrBits.CALL_STACK)
            return

        result = (val1 - val2) & ((1 << 32) - 1)
        state.gprs.get_reg(self.grd).write_unsigned(result)


class SLL(RV32RegReg):
    insn = insn_for_mnemonic('sll', 3)

    def execute(self, state: OTBNState) -> None:
        val1 = state.gprs.get_reg(self.grs1).read_unsigned()
        val2 = state.gprs.get_reg(self.grs2).read_unsigned() & 0x1f
        if state.gprs.call_stack_err:
            state.stop_at_end_of_cycle(ErrBits.CALL_STACK)
            return

        result = (val1 << val2) & ((1 << 32) - 1)
        state.gprs.get_reg(self.grd).write_unsigned(result)


class SLLI(RV32ImmShift):
    insn = insn_for_mnemonic('slli', 3)

    def execute(self, state: OTBNState) -> None:
        val1 = state.gprs.get_reg(self.grs1).read_unsigned()
        if state.gprs.call_stack_err:
            state.stop_at_end_of_cycle(ErrBits.CALL_STACK)
            return

        result = (val1 << self.shamt) & ((1 << 32) - 1)
        state.gprs.get_reg(self.grd).write_unsigned(result)


class SRL(RV32RegReg):
    insn = insn_for_mnemonic('srl', 3)

    def execute(self, state: OTBNState) -> None:
        val1 = state.gprs.get_reg(self.grs1).read_unsigned()
        val2 = state.gprs.get_reg(self.grs2).read_unsigned() & 0x1f
        if state.gprs.call_stack_err:
            state.stop_at_end_of_cycle(ErrBits.CALL_STACK)
            return

        result = val1 >> val2
        state.gprs.get_reg(self.grd).write_unsigned(result)


class SRLI(RV32ImmShift):
    insn = insn_for_mnemonic('srli', 3)

    def execute(self, state: OTBNState) -> None:
        val1 = state.gprs.get_reg(self.grs1).read_unsigned()
        if state.gprs.call_stack_err:
            state.stop_at_end_of_cycle(ErrBits.CALL_STACK)
            return

        result = val1 >> self.shamt
        state.gprs.get_reg(self.grd).write_unsigned(result)


class SRA(RV32RegReg):
    insn = insn_for_mnemonic('sra', 3)

    def execute(self, state: OTBNState) -> None:
        val1 = state.gprs.get_reg(self.grs1).read_signed()
        val2 = state.gprs.get_reg(self.grs2).read_unsigned() & 0x1f
        if state.gprs.call_stack_err:
            state.stop_at_end_of_cycle(ErrBits.CALL_STACK)
            return

        result = val1 >> val2
        state.gprs.get_reg(self.grd).write_signed(result)


class SRAI(RV32ImmShift):
    insn = insn_for_mnemonic('srai', 3)

    def execute(self, state: OTBNState) -> None:
        val1 = state.gprs.get_reg(self.grs1).read_signed()
        val2 = self.shamt
        if state.gprs.call_stack_err:
            state.stop_at_end_of_cycle(ErrBits.CALL_STACK)
            return

        result = val1 >> val2
        state.gprs.get_reg(self.grd).write_signed(result)


class AND(RV32RegReg):
    insn = insn_for_mnemonic('and', 3)

    def execute(self, state: OTBNState) -> None:
        val1 = state.gprs.get_reg(self.grs1).read_unsigned()
        val2 = state.gprs.get_reg(self.grs2).read_unsigned()
        if state.gprs.call_stack_err:
            state.stop_at_end_of_cycle(ErrBits.CALL_STACK)
            return

        result = val1 & val2
        state.gprs.get_reg(self.grd).write_unsigned(result)


class ANDI(RV32RegImm):
    insn = insn_for_mnemonic('andi', 3)

    def execute(self, state: OTBNState) -> None:
        val1 = state.gprs.get_reg(self.grs1).read_unsigned()
        val2 = self.to_2s_complement(self.imm)
        if state.gprs.call_stack_err:
            state.stop_at_end_of_cycle(ErrBits.CALL_STACK)
            return

        result = val1 & val2
        state.gprs.get_reg(self.grd).write_unsigned(result)


class OR(RV32RegReg):
    insn = insn_for_mnemonic('or', 3)

    def execute(self, state: OTBNState) -> None:
        val1 = state.gprs.get_reg(self.grs1).read_unsigned()
        val2 = state.gprs.get_reg(self.grs2).read_unsigned()
        if state.gprs.call_stack_err:
            state.stop_at_end_of_cycle(ErrBits.CALL_STACK)
            return

        result = val1 | val2
        state.gprs.get_reg(self.grd).write_unsigned(result)


class ORI(RV32RegImm):
    insn = insn_for_mnemonic('ori', 3)

    def execute(self, state: OTBNState) -> None:
        val1 = state.gprs.get_reg(self.grs1).read_unsigned()
        val2 = self.to_2s_complement(self.imm)
        if state.gprs.call_stack_err:
            state.stop_at_end_of_cycle(ErrBits.CALL_STACK)
            return

        result = val1 | val2
        state.gprs.get_reg(self.grd).write_unsigned(result)


class XOR(RV32RegReg):
    insn = insn_for_mnemonic('xor', 3)

    def execute(self, state: OTBNState) -> None:
        val1 = state.gprs.get_reg(self.grs1).read_unsigned()
        val2 = state.gprs.get_reg(self.grs2).read_unsigned()
        if state.gprs.call_stack_err:
            state.stop_at_end_of_cycle(ErrBits.CALL_STACK)
            return

        result = val1 ^ val2
        state.gprs.get_reg(self.grd).write_unsigned(result)


class XORI(RV32RegImm):
    insn = insn_for_mnemonic('xori', 3)

    def execute(self, state: OTBNState) -> None:
        val1 = state.gprs.get_reg(self.grs1).read_unsigned()
        val2 = self.to_2s_complement(self.imm)
        if state.gprs.call_stack_err:
            state.stop_at_end_of_cycle(ErrBits.CALL_STACK)
            return

        result = val1 ^ val2
        state.gprs.get_reg(self.grd).write_unsigned(result)


class LW(OTBNInsn):
    insn = insn_for_mnemonic('lw', 3)

    def __init__(self, raw: int, op_vals: Dict[str, int]):
        super().__init__(raw, op_vals)
        self.grd = op_vals['grd']
        self.offset = op_vals['offset']
        self.grs1 = op_vals['grs1']

    def execute(self, state: OTBNState) -> Optional[Iterator[None]]:
        # LW executes over two cycles. On the first cycle, we read the base
        # address, compute the load address and check it for correctness, then
        # perform the load itself, returning the result.
        #
        # On the second cycle, we write the result to the destination register.

        base = state.gprs.get_reg(self.grs1).read_unsigned()
        if state.gprs.call_stack_err:
            state.stop_at_end_of_cycle(ErrBits.CALL_STACK)
            return None

        addr = (base + self.offset) & ((1 << 32) - 1)

        if not state.dmem.is_valid_32b_addr(addr):
            state.stop_at_end_of_cycle(ErrBits.BAD_DATA_ADDR)
            return None

        result, valid = state.dmem.load_u32(addr)

        # Stall for a single cycle for memory to respond
        yield None

        if not valid:
            state.stop_at_end_of_cycle(ErrBits.DMEM_INTG_VIOLATION)

        state.gprs.get_reg(self.grd).write_unsigned(result)
        return None


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

        bad_grs1 = state.gprs.call_stack_err and (self.grs1 == 1)

        saw_err = False

        if state.gprs.call_stack_err:
            state.stop_at_end_of_cycle(ErrBits.CALL_STACK)
            saw_err = True

        if not state.dmem.is_valid_32b_addr(addr) and not bad_grs1:
            state.stop_at_end_of_cycle(ErrBits.BAD_DATA_ADDR)
            saw_err = True

        if saw_err:
            return

        state.dmem.store_u32(addr, value)


class BEQ(OTBNInsn):
    insn = insn_for_mnemonic('beq', 3)
    affects_control = True
    has_fetch_stall = True

    def __init__(self, raw: int, op_vals: Dict[str, int]):
        super().__init__(raw, op_vals)
        self.grs1 = op_vals['grs1']
        self.grs2 = op_vals['grs2']
        self.offset = op_vals['offset']

    def execute(self, state: OTBNState) -> None:
        val1 = state.gprs.get_reg(self.grs1).read_unsigned()
        val2 = state.gprs.get_reg(self.grs2).read_unsigned()
        if state.gprs.call_stack_err:
            state.stop_at_end_of_cycle(ErrBits.CALL_STACK)
            return

        tgt_pc = self.offset & ((1 << 32) - 1)
        if val1 == val2:
            if not state.is_pc_valid(tgt_pc):
                state.stop_at_end_of_cycle(ErrBits.BAD_INSN_ADDR)
            else:
                state.set_next_pc(tgt_pc)


class BNE(OTBNInsn):
    insn = insn_for_mnemonic('bne', 3)
    affects_control = True
    has_fetch_stall = True

    def __init__(self, raw: int, op_vals: Dict[str, int]):
        super().__init__(raw, op_vals)
        self.grs1 = op_vals['grs1']
        self.grs2 = op_vals['grs2']
        self.offset = op_vals['offset']

    def execute(self, state: OTBNState) -> None:
        val1 = state.gprs.get_reg(self.grs1).read_unsigned()
        val2 = state.gprs.get_reg(self.grs2).read_unsigned()

        if state.gprs.call_stack_err:
            state.stop_at_end_of_cycle(ErrBits.CALL_STACK)
            return

        tgt_pc = self.offset & ((1 << 32) - 1)
        if val1 != val2:
            if not state.is_pc_valid(tgt_pc):
                state.stop_at_end_of_cycle(ErrBits.BAD_INSN_ADDR)
            else:
                state.set_next_pc(tgt_pc)


class JAL(OTBNInsn):
    insn = insn_for_mnemonic('jal', 2)
    affects_control = True
    has_fetch_stall = True

    def __init__(self, raw: int, op_vals: Dict[str, int]):
        super().__init__(raw, op_vals)
        self.grd = op_vals['grd']
        self.offset = op_vals['offset']

    def execute(self, state: OTBNState) -> None:
        mask32 = ((1 << 32) - 1)
        link_pc = (state.pc + 4) & mask32
        state.gprs.get_reg(self.grd).write_unsigned(link_pc)

        next_pc = self.offset & mask32
        if not state.is_pc_valid(next_pc):
            state.stop_at_end_of_cycle(ErrBits.BAD_INSN_ADDR)
        else:
            state.set_next_pc(next_pc)


class JALR(OTBNInsn):
    insn = insn_for_mnemonic('jalr', 3)
    affects_control = True
    has_fetch_stall = True

    def __init__(self, raw: int, op_vals: Dict[str, int]):
        super().__init__(raw, op_vals)
        self.grd = op_vals['grd']
        self.grs1 = op_vals['grs1']
        self.offset = op_vals['offset']

    def execute(self, state: OTBNState) -> None:
        val1 = state.gprs.get_reg(self.grs1).read_unsigned()
        if state.gprs.call_stack_err:
            state.stop_at_end_of_cycle(ErrBits.CALL_STACK)
            return

        mask32 = ((1 << 32) - 1)
        link_pc = (state.pc + 4) & mask32

        state.gprs.get_reg(self.grd).write_unsigned(link_pc)

        next_pc = (val1 + self.offset) & mask32
        if not state.is_pc_valid(next_pc):
            state.stop_at_end_of_cycle(ErrBits.BAD_INSN_ADDR)
        else:
            state.set_next_pc(next_pc)


class CSRRS(OTBNInsn):
    insn = insn_for_mnemonic('csrrs', 3)

    def __init__(self, raw: int, op_vals: Dict[str, int]):
        super().__init__(raw, op_vals)
        self.grd = op_vals['grd']
        self.csr = op_vals['csr']
        self.grs1 = op_vals['grs1']

    def execute(self, state: OTBNState) -> Optional[Iterator[None]]:
        if not state.csrs.check_idx(self.csr):
            # Invalid CSR index. Stop with an illegal instruction error.
            state.stop_at_end_of_cycle(ErrBits.ILLEGAL_INSN)
            return None

        bits_to_set = state.gprs.get_reg(self.grs1).read_unsigned()
        if state.gprs.call_stack_err:
            state.stop_at_end_of_cycle(ErrBits.CALL_STACK)
            return None

        if self.csr == 0xfc0:
            # A read from RND. If a RND value is not available, request_value()
            # initiates or continues an EDN request and returns False. If a RND
            # value is available, it returns True.
            while not state.wsrs.RND.request_value():
                # There's a pending EDN request. Stall for a cycle.
                yield None

        # At this point, the CSR is ready. Read, update and write back to grs1.
        old_val = state.read_csr(self.csr)
        new_val = old_val | bits_to_set
        state.gprs.get_reg(self.grd).write_unsigned(old_val)
        if self.grs1 != 0:
            state.write_csr(self.csr, new_val)

        return None


class CSRRW(OTBNInsn):
    insn = insn_for_mnemonic('csrrw', 3)

    def __init__(self, raw: int, op_vals: Dict[str, int]):
        super().__init__(raw, op_vals)
        self.grd = op_vals['grd']
        self.csr = op_vals['csr']
        self.grs1 = op_vals['grs1']

    def execute(self, state: OTBNState) -> Optional[Iterator[None]]:
        if not state.csrs.check_idx(self.csr):
            # Invalid CSR index. Stop with an illegal instruction error.
            state.stop_at_end_of_cycle(ErrBits.ILLEGAL_INSN)
            return None

        new_val = state.gprs.get_reg(self.grs1).read_unsigned()
        if state.gprs.call_stack_err:
            state.stop_at_end_of_cycle(ErrBits.CALL_STACK)
            return None

        if self.csr == 0xfc0 and self.grd != 0:
            # A read from RND. If a RND value is not available, request_value()
            # initiates or continues an EDN request and returns False. If a RND
            # value is available, it returns True.
            while not state.wsrs.RND.request_value():
                # There's a pending EDN request. Stall for a cycle.
                yield None

        # At this point, the CSR is either ready or unneeded. Read it if
        # necessary and write to grd, then overwrite with new_val.

        if self.grd != 0:
            old_val = state.read_csr(self.csr)
            state.gprs.get_reg(self.grd).write_unsigned(old_val)

        state.write_csr(self.csr, new_val)
        return None


class ECALL(OTBNInsn):
    insn = insn_for_mnemonic('ecall', 0)

    def execute(self, state: OTBNState) -> None:
        # Set INTR_STATE.done and STATUS, reflecting the fact we've stopped.
        state.stop_at_end_of_cycle(err_bits=0)


class LOOP(OTBNInsn):
    insn = insn_for_mnemonic('loop', 2)
    affects_control = True

    def __init__(self, raw: int, op_vals: Dict[str, int]):
        super().__init__(raw, op_vals)
        self.grs = op_vals['grs']
        self.bodysize = op_vals['bodysize']

    def execute(self, state: OTBNState) -> None:
        num_iters = state.gprs.get_reg(self.grs).read_unsigned()
        if state.gprs.call_stack_err:
            state.stop_at_end_of_cycle(ErrBits.CALL_STACK)
            return

        if num_iters == 0:
            state.stop_at_end_of_cycle(ErrBits.LOOP)
        else:
            state.loop_start(num_iters, self.bodysize)


class LOOPI(OTBNInsn):
    insn = insn_for_mnemonic('loopi', 2)
    affects_control = True

    def __init__(self, raw: int, op_vals: Dict[str, int]):
        super().__init__(raw, op_vals)
        self.iterations = op_vals['iterations']
        self.bodysize = op_vals['bodysize']

    def execute(self, state: OTBNState) -> None:
        if self.iterations == 0:
            state.stop_at_end_of_cycle(ErrBits.LOOP)
        else:
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

        full_result = a + b_shifted
        mask256 = (1 << 256) - 1
        masked_result = full_result & mask256
        carry_flag = bool((full_result >> 256) & 1)
        flags = FlagReg.mlz_for_result(carry_flag, masked_result)

        state.wdrs.get_reg(self.wrd).write_unsigned(masked_result)
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
        full_result = a + b_shifted + carry
        mask256 = (1 << 256) - 1
        masked_result = full_result & mask256
        carry_flag = bool((full_result >> 256) & 1)
        flags = FlagReg.mlz_for_result(carry_flag, masked_result)

        state.wdrs.get_reg(self.wrd).write_unsigned(masked_result)
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

        full_result = a + b
        mask256 = (1 << 256) - 1
        masked_result = full_result & mask256
        carry_flag = bool((full_result >> 256) & 1)
        flags = FlagReg.mlz_for_result(carry_flag, masked_result)

        state.wdrs.get_reg(self.wrd).write_unsigned(masked_result)
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
        a = state.wdrs.get_reg(self.wrs1).read_unsigned()
        b = state.wdrs.get_reg(self.wrs2).read_unsigned()

        a_qw = extract_quarter_word(a, self.wrs1_qwsel)
        b_qw = extract_quarter_word(b, self.wrs2_qwsel)

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
        a = state.wdrs.get_reg(self.wrs1).read_unsigned()
        b = state.wdrs.get_reg(self.wrs2).read_unsigned()

        a_qw = extract_quarter_word(a, self.wrs1_qwsel)
        b_qw = extract_quarter_word(b, self.wrs2_qwsel)

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
        a = state.wdrs.get_reg(self.wrs1).read_unsigned()
        b = state.wdrs.get_reg(self.wrs2).read_unsigned()

        a_qw = extract_quarter_word(a, self.wrs1_qwsel)
        b_qw = extract_quarter_word(b, self.wrs2_qwsel)

        mul_res = a_qw * b_qw

        acc = state.wsrs.ACC.read_unsigned()
        if self.zero_acc:
            acc = 0

        acc += (mul_res << self.acc_shift_imm)
        truncated = acc & ((1 << 256) - 1)

        # Split the result into low and high parts
        lo_part = truncated & ((1 << 128) - 1)
        hi_part = truncated >> 128

        # Shift out the low part of the result
        hw_shift = 128 * self.wrd_hwsel
        hw_mask = ((1 << 128) - 1) << hw_shift
        old_wrd = state.wdrs.get_reg(self.wrd).read_unsigned()
        new_wrd = (old_wrd & ~hw_mask) | (lo_part << hw_shift)
        state.wdrs.get_reg(self.wrd).write_unsigned(new_wrd)

        # Write back the high part of the result
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
        state.set_flags(self.flag_group, new_flags)


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

        full_result = a - b_shifted
        mask256 = (1 << 256) - 1
        masked_result = full_result & mask256
        carry_flag = bool((full_result >> 256) & 1)
        flags = FlagReg.mlz_for_result(carry_flag, masked_result)

        state.wdrs.get_reg(self.wrd).write_unsigned(masked_result)
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

        full_result = a - b_shifted - borrow
        mask256 = (1 << 256) - 1
        masked_result = full_result & mask256
        carry_flag = bool((full_result >> 256) & 1)
        flags = FlagReg.mlz_for_result(carry_flag, masked_result)

        state.wdrs.get_reg(self.wrd).write_unsigned(masked_result)
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

        full_result = a - b
        mask256 = (1 << 256) - 1
        masked_result = full_result & mask256
        carry_flag = bool((full_result >> 256) & 1)
        flags = FlagReg.mlz_for_result(carry_flag, masked_result)

        state.wdrs.get_reg(self.wrd).write_unsigned(masked_result)
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


class BNSEL(OTBNInsn):
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

        full_result = a - b_shifted
        mask256 = (1 << 256) - 1
        masked_result = full_result & mask256
        carry_flag = bool((full_result >> 256) & 1)
        flags = FlagReg.mlz_for_result(carry_flag, masked_result)

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

        full_result = a - b_shifted - borrow
        mask256 = (1 << 256) - 1
        masked_result = full_result & mask256
        carry_flag = bool((full_result >> 256) & 1)
        flags = FlagReg.mlz_for_result(carry_flag, masked_result)

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

    def execute(self, state: OTBNState) -> Optional[Iterator[None]]:
        # BN.LID executes over two cycles. On the first cycle, we read the base
        # address, compute the load address and check it for correctness,
        # increment any GPRs, then perform the load itself. On the second
        # cycle, update the WDR with the result.

        if self.grs1_inc and self.grd_inc:
            state.stop_at_end_of_cycle(ErrBits.ILLEGAL_INSN)
            return None

        grs1_val = state.gprs.get_reg(self.grs1).read_unsigned()
        addr = (grs1_val + self.offset) & ((1 << 32) - 1)
        grd_val = state.gprs.get_reg(self.grd).read_unsigned()

        bad_grs1 = state.gprs.call_stack_err and (self.grs1 == 1)
        bad_grd = state.gprs.call_stack_err and (self.grd == 1)

        saw_err = False

        if state.gprs.call_stack_err:
            state.stop_at_end_of_cycle(ErrBits.CALL_STACK)
            saw_err = True

        if grd_val > 31 and not bad_grd:
            state.stop_at_end_of_cycle(ErrBits.ILLEGAL_INSN)
            saw_err = True

        if not state.dmem.is_valid_256b_addr(addr) and not bad_grs1:
            state.stop_at_end_of_cycle(ErrBits.BAD_DATA_ADDR)
            saw_err = True

        if saw_err:
            return None

        wrd = grd_val & 0x1f
        value, valid = state.dmem.load_u256(addr)

        if self.grd_inc:
            new_grd_val = grd_val + 1
            state.gprs.get_reg(self.grd).write_unsigned(new_grd_val)

        if self.grs1_inc:
            new_grs1_val = (grs1_val + 32) & ((1 << 32) - 1)
            state.gprs.get_reg(self.grs1).write_unsigned(new_grs1_val)

        # Stall for a single cycle for memory to respond
        yield None

        if not valid:
            state.stop_at_end_of_cycle(ErrBits.DMEM_INTG_VIOLATION)

        state.wdrs.get_reg(wrd).write_unsigned(value)
        return None


class BNSID(OTBNInsn):
    insn = insn_for_mnemonic('bn.sid', 5)

    def __init__(self, raw: int, op_vals: Dict[str, int]):
        super().__init__(raw, op_vals)
        self.grs2 = op_vals['grs2']
        self.grs2_inc = op_vals['grs2_inc']
        self.offset = op_vals['offset']
        self.grs1 = op_vals['grs1']
        self.grs1_inc = op_vals['grs1_inc']

    def execute(self, state: OTBNState) -> Optional[Iterator[None]]:
        if self.grs1_inc and self.grs2_inc:
            state.stop_at_end_of_cycle(ErrBits.ILLEGAL_INSN)
            return None

        grs1_val = state.gprs.get_reg(self.grs1).read_unsigned()
        addr = (grs1_val + self.offset) & ((1 << 32) - 1)
        grs2_val = state.gprs.get_reg(self.grs2).read_unsigned()

        bad_grs1 = state.gprs.call_stack_err and (self.grs1 == 1)
        bad_grs2 = state.gprs.call_stack_err and (self.grs2 == 1)

        saw_err = False

        if state.gprs.call_stack_err:
            state.stop_at_end_of_cycle(ErrBits.CALL_STACK)
            saw_err = True

        if grs2_val > 31 and not bad_grs2:
            state.stop_at_end_of_cycle(ErrBits.ILLEGAL_INSN)
            saw_err = True

        if not state.dmem.is_valid_256b_addr(addr) and not bad_grs1:
            state.stop_at_end_of_cycle(ErrBits.BAD_DATA_ADDR)
            saw_err = True

        if saw_err:
            return None

        if self.grs1_inc:
            new_grs1_val = (grs1_val + 32) & ((1 << 32) - 1)
            state.gprs.get_reg(self.grs1).write_unsigned(new_grs1_val)

        if self.grs2_inc:
            new_grs2_val = grs2_val + 1
            state.gprs.get_reg(self.grs2).write_unsigned(new_grs2_val)

        yield None

        wrs = grs2_val & 0x1f
        wrs_val = state.wdrs.get_reg(wrs).read_unsigned()

        state.dmem.store_u256(addr, wrs_val)
        return None


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

    def execute(self, state: OTBNState) -> Optional[Iterator[None]]:
        if self.grs_inc and self.grd_inc:
            state.stop_at_end_of_cycle(ErrBits.ILLEGAL_INSN)
            return None

        grd_val = state.gprs.get_reg(self.grd).read_unsigned()
        grs_val = state.gprs.get_reg(self.grs).read_unsigned()

        bad_grs = state.gprs.call_stack_err and (self.grs == 1)
        bad_grd = state.gprs.call_stack_err and (self.grd == 1)

        saw_err = False

        if state.gprs.call_stack_err:
            state.stop_at_end_of_cycle(ErrBits.CALL_STACK)
            saw_err = True

        if grd_val > 31 and not bad_grd:
            state.stop_at_end_of_cycle(ErrBits.ILLEGAL_INSN)
            saw_err = True

        if grs_val > 31 and not bad_grs:
            state.stop_at_end_of_cycle(ErrBits.ILLEGAL_INSN)
            saw_err = True

        if saw_err:
            return None

        wrd = grd_val & 0x1f
        wrs = grs_val & 0x1f

        if self.grd_inc:
            new_grd_val = grd_val + 1
            state.gprs.get_reg(self.grd).write_unsigned(new_grd_val)

        if self.grs_inc:
            new_grs_val = grs_val + 1
            state.gprs.get_reg(self.grs).write_unsigned(new_grs_val)

        yield None

        value = state.wdrs.get_reg(wrs).read_unsigned()
        state.wdrs.get_reg(wrd).write_unsigned(value)
        return None


class BNWSRR(OTBNInsn):
    insn = insn_for_mnemonic('bn.wsrr', 2)

    def __init__(self, raw: int, op_vals: Dict[str, int]):
        super().__init__(raw, op_vals)
        self.wrd = op_vals['wrd']
        self.wsr = op_vals['wsr']

    def execute(self, state: OTBNState) -> Optional[Iterator[None]]:
        # The first, and possibly only, cycle of execution.
        if not state.wsrs.check_idx(self.wsr):
            # Invalid WSR index. Stop with an illegal instruction error.
            state.stop_at_end_of_cycle(ErrBits.ILLEGAL_INSN)
            return None

        if self.wsr == 0x1:
            # A read from RND. If a RND value is not available, request_value()
            # initiates or continues an EDN request and returns False. If a RND
            # value is available, it returns True.
            while not state.wsrs.RND.request_value():
                # There's a pending EDN request. Stall for a cycle.
                yield None

        # At this point, the WSR is ready. Does it have a valid value? (It
        # might not if this is a sideload key register and keymgr hasn't
        # provided us with a value). If not, fail with a KEY_INVALID error.
        if not state.wsrs.has_value_at_idx(self.wsr):
            state.stop_at_end_of_cycle(ErrBits.KEY_INVALID)
            return None

        # The WSR is ready and has a value. Read it.
        val = state.wsrs.read_at_idx(self.wsr)

        state.wdrs.get_reg(self.wrd).write_unsigned(val)
        return None


class BNWSRW(OTBNInsn):
    insn = insn_for_mnemonic('bn.wsrw', 2)

    def __init__(self, raw: int, op_vals: Dict[str, int]):
        super().__init__(raw, op_vals)
        self.wsr = op_vals['wsr']
        self.wrs = op_vals['wrs']

    def execute(self, state: OTBNState) -> None:
        if not state.wsrs.check_idx(self.wsr):
            # Invalid WSR index. Stop with an illegal instruction error.
            state.stop_at_end_of_cycle(ErrBits.ILLEGAL_INSN)
            return None

        val = state.wdrs.get_reg(self.wrs).read_unsigned()

        state.wsrs.write_at_idx(self.wsr, val)


class BNADDV(BnVecVecAdd):
    insn = insn_for_mnemonic('bn.addv', 4)

    def execute(self, state: OTBNState) -> None:
        # The operation performed on the element pairs.
        def op(a: int, b: int) -> int:
            c = a + b
            return c

        vec_a = state.wdrs.get_reg(self.wrs1).read_unsigned()
        vec_b = state.wdrs.get_reg(self.wrs2).read_unsigned()
        size = element_length_in_bits(self.elen)

        # Invalid ELEN choice. Stop with an illegal instruction error.
        if size not in BNADDV.supported_elens:
            state.stop_at_end_of_cycle(ErrBits.ILLEGAL_INSN)
            return None

        result = map_elems(op, size, vec_a, vec_b)

        state.wdrs.get_reg(self.wrd).write_unsigned(result)


class BNADDVM(BnVecVecAdd):
    insn = insn_for_mnemonic('bn.addvm', 4)

    def execute(self, state: OTBNState) -> None:
        # The operation performed on the element pairs.
        def op(mod_val: int, a: int, b: int) -> int:
            c = a + b
            if c >= mod_val:
                c -= mod_val
            return c

        vec_a = state.wdrs.get_reg(self.wrs1).read_unsigned()
        vec_b = state.wdrs.get_reg(self.wrs2).read_unsigned()
        size = element_length_in_bits(self.elen)

        # Invalid ELEN choice. Stop with an illegal instruction error.
        if size not in BNADDVM.supported_elens:
            state.stop_at_end_of_cycle(ErrBits.ILLEGAL_INSN)
            return None

        # Extract the modulus from WSR MOD but only size bits as upper bits may contain the
        # Montgomery constant.
        mod_val = state.wsrs.MOD.read_unsigned() & ((1 << size) - 1)

        result = map_elems(lambda a, b: op(mod_val, a, b), size, vec_a, vec_b)

        state.wdrs.get_reg(self.wrd).write_unsigned(result)


class BNSUBV(BnVecVecAdd):
    insn = insn_for_mnemonic('bn.subv', 4)

    def execute(self, state: OTBNState) -> None:
        # The operation performed on the element pairs.
        def op(a: int, b: int) -> int:
            c = a - b
            return c

        vec_a = state.wdrs.get_reg(self.wrs1).read_unsigned()
        vec_b = state.wdrs.get_reg(self.wrs2).read_unsigned()
        size = element_length_in_bits(self.elen)

        # Invalid ELEN choice. Stop with an illegal instruction error.
        if size not in BNSUBV.supported_elens:
            state.stop_at_end_of_cycle(ErrBits.ILLEGAL_INSN)
            return None

        result = map_elems(op, size, vec_a, vec_b)

        state.wdrs.get_reg(self.wrd).write_unsigned(result)


class BNSUBVM(BnVecVecAdd):
    insn = insn_for_mnemonic('bn.subvm', 4)

    def execute(self, state: OTBNState) -> None:
        # The operation performed on the element pairs.
        def op(mod_val: int, a: int, b: int) -> int:
            c = a - b
            if c < 0:
                c += mod_val
            return c

        vec_a = state.wdrs.get_reg(self.wrs1).read_unsigned()
        vec_b = state.wdrs.get_reg(self.wrs2).read_unsigned()
        size = element_length_in_bits(self.elen)

        # Invalid ELEN choice. Stop with an illegal instruction error.
        if size not in BNSUBVM.supported_elens:
            state.stop_at_end_of_cycle(ErrBits.ILLEGAL_INSN)
            return None

        # Extract the modulus from WSR MOD.
        mod_val = state.wsrs.MOD.read_unsigned() & ((1 << size) - 1)

        result = map_elems(lambda a, b: op(mod_val, a, b), size, vec_a, vec_b)

        state.wdrs.get_reg(self.wrd).write_unsigned(result)


class BNMULV(BnVecVecMul):
    insn = insn_for_mnemonic('bn.mulv', 4)

    def execute(self, state: OTBNState) -> Optional[Iterator[None]]:
        # The operation performed on the element pairs.
        def op(a: int, b: int) -> int:
            c = a * b
            return c

        vec_a = state.wdrs.get_reg(self.wrs1).read_unsigned()
        vec_b = state.wdrs.get_reg(self.wrs2).read_unsigned()
        size = element_length_in_bits(self.elen)

        # Invalid ELEN choice. Stop with an illegal instruction error.
        if size not in BNMULV.supported_elens:
            state.stop_at_end_of_cycle(ErrBits.ILLEGAL_INSN)
            return None

        # This instruction operates over 4 cycles. In each cycle 64b of the 256b vector are
        # processed. We first compute the results and then emulate the register updates.
        result = map_elems(op, size, vec_a, vec_b)

        # Emulate the register updates
        # In the first cycle ACC is reset and the lowest quarter word is written.
        # In other cycles ACC is read and the corresponding quarter word is merged.
        # In the last cycle we also write the result to the destination WDR.
        qword_mask = (1 << 64) - 1
        for cycle in range(4):
            acc = 0 if cycle == 0 else state.wsrs.ACC.read_unsigned()
            current_qword_mask = qword_mask << (cycle * 64)
            acc |= result & current_qword_mask
            state.wsrs.ACC.write_unsigned(acc)
            if cycle < 3:
                yield None

        state.wdrs.get_reg(self.wrd).write_unsigned(result)


class BNMULVL(BnVecVecMul):
    insn = insn_for_mnemonic('bn.mulvl', 5)

    def __init__(self, raw: int, op_vals: Dict[str, int]):
        super().__init__(raw, op_vals)
        self.lane = op_vals['lane']

    def execute(self, state: OTBNState) -> Optional[Iterator[None]]:
        # The operation performed on the element pairs.
        def op(a: int, b: int) -> int:
            c = a * b
            return c

        vec_a = state.wdrs.get_reg(self.wrs1).read_unsigned()
        vec_b = state.wdrs.get_reg(self.wrs2).read_unsigned()
        size = element_length_in_bits(self.elen)

        # Invalid ELEN choice. Stop with an illegal instruction error.
        if size not in BNMULVL.supported_elens:
            state.stop_at_end_of_cycle(ErrBits.ILLEGAL_INSN)
            return None

        # This instruction operates over 4 cycles. In each cycle 64b of the 256b vector are
        # processed. We first compute the results and then emulate the register updates.

        # Replicate lane element to generate a 256b vector with 256/size elements.
        lane_elem = extract_vec_elem(vec_b, self.lane, size)
        lane_vec = 0
        for i in range(256 // size):
            lane_vec |= (lane_elem << (i * size))

        result = map_elems(op, size, vec_a, lane_vec)

        # Emulate the register updates
        # In the first cycle ACC is reset and the lowest quarter word is written.
        # In other cycles ACC is read and the corresponding quarter word is merged.
        # In the last cycle we also write the result to the destination WDR.
        qword_mask = (1 << 64) - 1
        for cycle in range(4):
            acc = 0 if cycle == 0 else state.wsrs.ACC.read_unsigned()
            current_qword_mask = qword_mask << (cycle * 64)
            acc |= result & current_qword_mask
            state.wsrs.ACC.write_unsigned(acc)
            if cycle < 3:
                yield None

        state.wdrs.get_reg(self.wrd).write_unsigned(result)


class BNMULVM(BnVecVecMul):
    insn = insn_for_mnemonic('bn.mulvm', 4)

    # This instruction performs a Montgomery multiplication without the final conditional
    # subtraction.
    #
    # Inputs for the Montgomery algorithm:
    # - a, b: Operands in [0, q[ in Montgomery space
    # - d:    Bit-width of operands
    # - q:    Modulus in ]0, 2^d]
    # - mu:   Montgomery constant, precomputed, mu = (-q)^(-1) mod 2^d
    #
    # The operands must be pre-transformed into Montgomery space with
    #   a = a_orig * 2^d mod q.
    # This must be ensured by the programmer.
    #
    # The Montgomery multiplication is defined as:
    #   r = a*b * 2^(-d) mod q
    # where r is in [0,q[.
    #
    # This can be computed with the following steps where `[]_d` are the lower `d` bits and `[]^d`
    # are the higher `d` bits:
    #   c = a*b
    #   r = [c + [[c]_d * mu]_d * q]^d
    #   if r >= q then // not implemented in hardware
    #       return r - q
    #   return r
    #
    # This instruction computes these steps except the final conditional subtraction (`r >= q`) to
    # optimize area and timing.
    #
    # To save resources the 64 bit MAC multiplier is reused and thus the calculations is split over
    # multiple cycles. The instruction requires 12 cycles in total where each 64b part is processed
    # in 3 cycles.
    #   Cycle 0:  Reg(Tmp) = 0, Reg(C) = 0
    #   Cycle 1:  Reg(Tmp) = [a*b]_d,     Reg(C) = a*b
    #   Cycle 2:  Reg(Tmp) = [Tmp*mu]_d,  Reg(C) = a*b
    #   Cycle 3:  Output   = c + (Tmp)*q mod q = [c + (Tmp)*q]^d (-q)
    #
    # The required constants q and mu are expected to be in the MOD WSR at following locations:
    # For .8s: q @ [31:0], mu @ [63:32]
    def execute(self, state: OTBNState) -> Optional[Iterator[None]]:
        # The operation performed on the element pairs.
        def op(a: int, b: int, q: int, mu: int, size: int) -> int:
            return montgomery_mul_no_cond_subtraction(a, b, q, mu, size)

        vec_a = state.wdrs.get_reg(self.wrs1).read_unsigned()
        vec_b = state.wdrs.get_reg(self.wrs2).read_unsigned()
        size = element_length_in_bits(self.elen)

        # Invalid ELEN choice. Stop with an illegal instruction error.
        if size not in BNMULVM.supported_elens:
            state.stop_at_end_of_cycle(ErrBits.ILLEGAL_INSN)
            return None

        # Extract the Montgomery constants q and mu
        mod_raw = state.wsrs.MOD.read_unsigned()
        offset_mu = size
        mod_q = mod_raw & ((1 << size) - 1)
        mod_mu = (mod_raw >> offset_mu) & ((1 << size) - 1)

        # We first compute the result and then emulate the register update sequence. We do model
        # only the ACC updates. We do not model the MAC's internal registers.
        result = map_elems(lambda a, b: op(a, b, mod_q, mod_mu, size), size, vec_a, vec_b)

        # Emulate the ACC register updates.
        # One 64b chunk computation requires 3 cycles. We perform the following register accesses
        # Cycle 1: TMP and C are written (internal registers, not modelled)
        # Cycle 2: TMP is written, ACC and C unused
        # Cycle 3: ACC is read and written, TMP and C are read
        #
        # We now repeat these 3 cycles for all four 64b chunks (quarter words).
        # When capturing the first QWord result, the ACC is cleared.
        # In cycle 12 we also write the result to the destination WDR
        qword_mask = (1 << 64) - 1
        for qword in range(4):
            # For the first QWord the first cycle is the one when the loop starts.
            if qword != 0:
                yield None
            yield None
            yield None
            acc = 0 if qword == 0 else state.wsrs.ACC.read_unsigned()
            current_qword_mask = qword_mask << (qword * 64)
            acc |= result & current_qword_mask
            state.wsrs.ACC.write_unsigned(acc)

        state.wdrs.get_reg(self.wrd).write_unsigned(result)


class BNMULVML(BnVecVecMul):
    insn = insn_for_mnemonic('bn.mulvml', 5)

    def __init__(self, raw: int, op_vals: Dict[str, int]):
        super().__init__(raw, op_vals)
        self.lane = op_vals['lane']

    # See BNMULVM for detailed explanation of instruction
    def execute(self, state: OTBNState) -> Optional[Iterator[None]]:
        def op(a: int, b: int, q: int, mu: int, size: int) -> int:
            return montgomery_mul_no_cond_subtraction(a, b, q, mu, size)

        vec_a = state.wdrs.get_reg(self.wrs1).read_unsigned()
        vec_b = state.wdrs.get_reg(self.wrs2).read_unsigned()
        size = element_length_in_bits(self.elen)

        # Invalid ELEN choice. Stop with an illegal instruction error.
        if size not in BNMULVML.supported_elens:
            state.stop_at_end_of_cycle(ErrBits.ILLEGAL_INSN)
            return None

        # Extract the Montgomery constants q and mu
        mod_raw = state.wsrs.MOD.read_unsigned()
        offset_mu = size
        mod_q = mod_raw & ((1 << size) - 1)
        mod_mu = (mod_raw >> offset_mu) & ((1 << size) - 1)

        # This instruction operates over 12 cycles. We first compute the results and then emulate
        # the register updates.

        # Replicate lane element to generate a 256b vector with 256/size elements.
        lane_elem = extract_vec_elem(vec_b, self.lane, size)
        lane_vec = 0
        for i in range(256 // size):
            lane_vec |= (lane_elem << (i * size))

        result = map_elems(lambda a, b: op(a, b, mod_q, mod_mu, size), size, vec_a, lane_vec)

        # Emulate the register updates. See BN.MULVM for details.
        qword_mask = (1 << 64) - 1
        for qword in range(4):
            # For the first QWord the first cycle is the one when the loop starts.
            if qword != 0:
                yield None
            yield None
            yield None
            acc = 0 if qword == 0 else state.wsrs.ACC.read_unsigned()
            current_qword_mask = qword_mask << (qword * 64)
            acc |= result & current_qword_mask
            state.wsrs.ACC.write_unsigned(acc)

        state.wdrs.get_reg(self.wrd).write_unsigned(result)


class BNTRN1(BnVecVecTrn):
    insn = insn_for_mnemonic('bn.trn1', 4)

    def execute(self, state: OTBNState) -> None:
        vec_a = state.wdrs.get_reg(self.wrs1).read_unsigned()
        vec_b = state.wdrs.get_reg(self.wrs2).read_unsigned()
        size = element_length_in_bits(self.elen)

        # Invalid ELEN choice. Stop with an illegal instruction error.
        if size not in BNTRN1.supported_elens:
            state.stop_at_end_of_cycle(ErrBits.ILLEGAL_INSN)
            return None

        vec_c = 0
        for elem in range(0, 256 // size, 2):
            elem_a = extract_vec_elem(vec_a, elem, size)
            elem_b = extract_vec_elem(vec_b, elem, size)

            vec_c = vec_c | ((elem_a) << (elem * size))
            vec_c = vec_c | ((elem_b) << ((elem + 1) * size))

        state.wdrs.get_reg(self.wrd).write_unsigned(vec_c)


class BNTRN2(BnVecVecTrn):
    insn = insn_for_mnemonic('bn.trn2', 4)

    def execute(self, state: OTBNState) -> None:
        vec_a = state.wdrs.get_reg(self.wrs1).read_unsigned()
        vec_b = state.wdrs.get_reg(self.wrs2).read_unsigned()
        size = element_length_in_bits(self.elen)

        # Invalid ELEN choice. Stop with an illegal instruction error.
        if size not in BNTRN2.supported_elens:
            state.stop_at_end_of_cycle(ErrBits.ILLEGAL_INSN)
            return None

        vec_c = 0
        for elem in range(0, 256 // size, 2):
            elem_a = extract_vec_elem(vec_a, elem + 1, size)
            elem_b = extract_vec_elem(vec_b, elem + 1, size)

            vec_c = vec_c | ((elem_a) << (elem * size))
            vec_c = vec_c | ((elem_b) << ((elem + 1) * size))

        state.wdrs.get_reg(self.wrd).write_unsigned(vec_c)


class BNSHV(OTBNInsn):
    insn = insn_for_mnemonic('bn.shv', 5)
    supported_elens = [32]

    def __init__(self, raw: int, op_vals: Dict[str, int]):
        super().__init__(raw, op_vals)
        self.wrd = op_vals['wrd']
        self.wrs1 = op_vals['wrs']
        self.elen = op_vals['elen']
        self.shift_type = op_vals['shift_type']
        self.shift_bits = op_vals['shift_bits']

    def execute(self, state: OTBNState) -> None:
        vec_a = state.wdrs.get_reg(self.wrs1).read_unsigned()
        size = element_length_in_bits(self.elen)

        # Invalid ELEN choice. Stop with an illegal instruction error.
        if size not in BNSHV.supported_elens:
            state.stop_at_end_of_cycle(ErrBits.ILLEGAL_INSN)
            return None

        vec_c = 0
        for elem in range(256 // size):
            elem_a = extract_vec_elem(vec_a, elem, size)
            elem_a_shifted = shift_vec_elem(elem_a, size, self.shift_type, self.shift_bits)
            vec_c = vec_c | (elem_a_shifted << (elem * size))

        state.wdrs.get_reg(self.wrd).write_unsigned(vec_c)


class BNUNPK(OTBNInsn):
    insn = insn_for_mnemonic('bn.unpk', 4)

    def __init__(self, raw: int, op_vals: Dict[str, int]):
        super().__init__(raw, op_vals)
        self.wrd = op_vals['wrd']
        self.wrs1 = op_vals['wrs1']
        self.wrs2 = op_vals['wrs2']
        self.shift = op_vals['shift_bits']

    def execute(self, state: OTBNState) -> None:
        vec_a = state.wdrs.get_reg(self.wrs1).read_unsigned()
        vec_b = state.wdrs.get_reg(self.wrs2).read_unsigned()

        # Concatenate to 512 bits and shift
        combined = (vec_a << 256) | (vec_b)
        shifted = combined >> self.shift

        # Unpack 8 24-bit elements into 32-bit elements
        unpacked = 0
        for elem in range(256 // 32):
            chunk = (shifted >> (elem * 24)) & ((1 << 24) - 1)
            unpacked = unpacked | (chunk << (elem * 32))

        state.wdrs.get_reg(self.wrd).write_unsigned(unpacked)


class BNPACK(OTBNInsn):
    insn = insn_for_mnemonic('bn.pack', 4)

    def __init__(self, raw: int, op_vals: Dict[str, int]):
        super().__init__(raw, op_vals)
        self.wrd = op_vals['wrd']
        self.wrs1 = op_vals['wrs1']
        self.wrs2 = op_vals['wrs2']
        self.shift = op_vals['shift_bits']

    def execute(self, state: OTBNState) -> None:
        vec_a = state.wdrs.get_reg(self.wrs1).read_unsigned()
        vec_b = state.wdrs.get_reg(self.wrs2).read_unsigned()

        # Pack 8 24b elements from 256b string into 192b string
        def pack_24b_elems(vec: int) -> int:
            dense = 0
            for elem in range(256 // 32):
                elem_a = (vec >> (elem * 32)) & ((1 << 24) - 1)
                dense = dense | (elem_a << (elem * 24))
            return dense

        dense_a = pack_24b_elems(vec_a)
        dense_b = pack_24b_elems(vec_b)

        # Concatenate and append 64 zeros to the right.
        combined = (dense_a << (192 + 64)) | (dense_b << 64)
        shifted = combined >> self.shift
        packed = shifted & ((1 << 256) - 1)

        state.wdrs.get_reg(self.wrd).write_unsigned(packed)


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
    BNSEL,
    BNCMP, BNCMPB,
    BNLID, BNSID,
    BNMOV, BNMOVR,
    BNWSRR, BNWSRW,

    BNADDV, BNADDVM,
    BNSUBV, BNSUBVM,
    BNMULV, BNMULVL,
    BNMULVM, BNMULVML,
    BNTRN1, BNTRN2,
    BNSHV,
    BNUNPK, BNPACK
]
