# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from typing import Optional

from shared.insn_yaml import InsnsFile

from ..config import Config
from ..model import Model
from ..program import ProgInsn, Program

from ..snippet import ProgSnippet
from ..snippet_gen import GenCont, GenRet, SnippetGen


class KnownWDR(SnippetGen):
    '''A snippet generator that generates known values (all zeros or all ones
    for now) for WDRs.

    '''

    def __init__(self, cfg: Config, insns_file: InsnsFile) -> None:
        super().__init__()

        self.bn_xor = self._get_named_insn(insns_file, 'bn.xor')
        self.bn_not = self._get_named_insn(insns_file, 'bn.not')
        self.imm_op_type = self.bn_xor.operands[4].op_type

    def gen(self,
            cont: GenCont,
            model: Model,
            program: Program) -> Optional[GenRet]:
        # Return None if this one of the last two instructions in the current
        # gap because we need to either jump or do an ECALL to avoid getting
        # stuck after executing both bn.xor and bn.not
        if program.get_insn_space_at(model.pc) <= 3:
            return None

        # The bn.xor-bn.not pair takes 2 instructions
        if program.space < 2:
            return None

        if model.fuel < 2:
            return None

        # Picks a random operand value for wrd.
        wrd_val_xor = model.pick_operand_value(self.bn_xor.operands[0].op_type)
        if wrd_val_xor is None:
            return None

        # Picks a random operand value. It shouldn't matter because
        # in the end, we will feed the same value as wrs2 and XORing
        # would result with wrd becoming 0.
        wrs_val_xor = model.pick_operand_value(self.bn_xor.operands[1].op_type)
        if wrs_val_xor is None:
            return None

        # Assertion is always true because ImmOperand has width embedded in it
        shift_bits = self.imm_op_type.op_val_to_enc_val(0, model.pc)
        assert shift_bits is not None

        # Value of shift_type does not matter since shift_bits are hardcoded to
        # 0
        shift_type = model.pick_operand_value(self.bn_xor.operands[3].op_type)
        assert shift_type is not None

        # This value does not matter for this application
        flg_group = model.pick_operand_value(self.bn_xor.operands[5].op_type)
        assert flg_group is not None

        # Result of this insn can be written to any register.
        wrd_val_not = model.pick_operand_value(self.bn_not.operands[0].op_type)
        if wrd_val_not is None:
            return None

        op_vals_xor = [wrd_val_xor, wrs_val_xor, wrs_val_xor, shift_type,
                       shift_bits, flg_group]

        op_vals_not = [wrd_val_not, wrs_val_xor,
                       shift_type, shift_bits, flg_group]

        prog_bn_xor = ProgInsn(self.bn_xor, op_vals_xor, None)
        prog_bn_not = ProgInsn(self.bn_not, op_vals_not, None)

        snippet = ProgSnippet(model.pc, [prog_bn_xor, prog_bn_not])
        snippet.insert_into_program(program)

        model.update_for_insn(prog_bn_xor)
        model.update_for_insn(prog_bn_not)

        model.pc += 8

        return (snippet, model)
