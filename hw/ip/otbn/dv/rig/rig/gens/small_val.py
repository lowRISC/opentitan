# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import random
from typing import Optional

from shared.operand import ImmOperandType, RegOperandType
from shared.insn_yaml import InsnsFile

from ..config import Config
from ..model import Model
from ..program import ProgInsn, Program
from ..snippet import ProgSnippet
from ..snippet_gen import GenCont, GenRet, SnippetGen


class SmallVal(SnippetGen):
    '''A snippet generator that generates writes small values to registers

    We do so using addi (which is modelled fully in model.py), which means we
    can then use those small values for later instructions: useful for things
    like loop counters.

    '''

    def __init__(self, cfg: Config, insns_file: InsnsFile) -> None:
        super().__init__()

        if 'addi' not in insns_file.mnemonic_to_insn:
            raise RuntimeError('ADDI instruction not in instructions file')
        self.insn = insns_file.mnemonic_to_insn['addi']

        # ADDI has three operands: grd, grs1 and imm.
        if not (len(self.insn.operands) == 3 and
                isinstance(self.insn.operands[0].op_type, RegOperandType) and
                self.insn.operands[0].op_type.reg_type == 'gpr' and
                isinstance(self.insn.operands[1].op_type, RegOperandType) and
                self.insn.operands[1].op_type.reg_type == 'gpr' and
                isinstance(self.insn.operands[2].op_type, ImmOperandType) and
                self.insn.operands[2].op_type.signed):
            raise RuntimeError('ADDI instruction from instructions file is not '
                               'the shape expected by the SmallVal generator.')

        self.grd_op_type = self.insn.operands[0].op_type
        self.grs1_op_type = self.insn.operands[1].op_type
        self.imm_op_type = self.insn.operands[2].op_type

    def gen(self,
            cont: GenCont,
            model: Model,
            program: Program) -> Optional[GenRet]:
        # Return None if this is the last instruction in the current gap
        # because we need to either jump or do an ECALL to avoid getting stuck.
        if program.get_insn_space_at(model.pc) <= 1:
            return None

        # Pick grd any old way: we can write to any register. This should
        # always succeed.
        grd_val = model.pick_operand_value(self.grd_op_type)
        assert grd_val is not None

        # Pick a target value. For now, we take arbitrary values in the range
        # [-64, 64]. Ideally ten percent of the time we want to have a random
        # value that is actually divisible by 32. That way we would have valid
        # registers that have values to point as WDR addresses for BN.XID
        # Other values are for helping with the misaligned address calculations
        temp_val = random.randint(-64, 64)
        gen_for_bn = random.randint(0, 9)

        shifts = {0: 5, 1: 1, 2: 2}
        tgt_val = temp_val << shifts.get(gen_for_bn, 0)

        # We'll use x0 as the register source. Since the register source has
        # value zero, we need -tgt_val as our immediate. The small range of
        # possible target values should mean this is always representable.
        imm_encoded = self.imm_op_type.op_val_to_enc_val(-tgt_val, model.pc)
        assert imm_encoded is not None

        op_vals = [grd_val, 0, imm_encoded]

        prog_insn = ProgInsn(self.insn, op_vals, None)
        snippet = ProgSnippet(model.pc, [prog_insn])
        snippet.insert_into_program(program)

        model.update_for_insn(prog_insn)
        model.pc += 4

        return (snippet, False, model)
