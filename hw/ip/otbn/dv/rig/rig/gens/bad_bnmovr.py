# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import random
from typing import Optional

from shared.operand import RegOperandType, OptionOperandType
from shared.insn_yaml import InsnsFile

from ..config import Config
from ..model import Model
from ..program import ProgInsn, Program

from ..snippet import ProgSnippet
from ..snippet_gen import GenCont, GenRet, SnippetGen


class BadBNMovr(SnippetGen):
    '''A snippet generator that generates program ending BN.MOVR instructions.

    This includes incrementing both GPRs or having *grd or *grs > 31

    '''

    ends_program = True

    def __init__(self, cfg: Config, insns_file: InsnsFile) -> None:
        super().__init__()

        self.insn = self._get_named_insn(insns_file, 'bn.movr')

        # bn.movr expects the operands: grd, grs, grd_inc, grs_inc
        if len(self.insn.operands) != 4:
            raise RuntimeError('Unexpected number of operands for bn.movr')

        grd, grs, grd_inc, grs_inc = self.insn.operands
        exp_shape = (
            # grd
            isinstance(grd.op_type, RegOperandType) and
            grd.op_type.reg_type == 'gpr' and
            not grd.op_type.is_dest() and
            # grs
            isinstance(grs.op_type, RegOperandType) and
            grs.op_type.reg_type == 'gpr' and
            not grs.op_type.is_dest() and
            # grd_inc
            isinstance(grd_inc.op_type, OptionOperandType) and
            # grs_inc
            isinstance(grs_inc.op_type, OptionOperandType)
        )
        if not exp_shape:
            raise RuntimeError('Unexpected shape for bn.movr')

        self.weight = cfg.insn_weights.get(self.insn.mnemonic)

        # Check that the instruction has a positive weight
        if not self.weight:
            self.disabled = True

    def gen(self,
            cont: GenCont,
            model: Model,
            program: Program) -> Optional[GenRet]:

        # Get known registers
        known_regs = model.regs_with_known_vals('gpr')
        bad_regs = []
        good_regs = []

        # Make sure there is at least one out of bounds value
        for reg_idx, reg_val in known_regs:
            if 31 < reg_val:
                bad_regs.append(reg_idx)
            else:
                good_regs.append(reg_idx)

        # We have 4 different options for increments * 4 different options for
        # out of bound register values.
        # reg_val_choice[1:0] ->   grd_val, grs_val
        # inc_choice[1:0]     ->   grd_inc, grs_inc
        # bad = 1, good = 0
        # choices[3:0] = {reg_val_choice, inc_choice}

        # We always have an element (x0) in good_regs but if bad_regs is empty
        # hard-code grd_val/grs_val = Good/Good and we have to use two incr.
        # for producing an error.
        choices = 3 if not bad_regs else random.randint(3, 15)

        reg_val_choice = choices // 4
        inc_choice = choices % 4

        bad_grd = reg_val_choice in [2, 3]  # grd_val/grs_val = Bad/Good or Bad/Bad
        bad_grs = reg_val_choice in [1, 3]  # grd_val/grs_val = Good/Bad or Bad/Bad

        # If grs_val/grd_val = good/good, we have to force +/+ for a fault
        grd_inc = int(inc_choice in [2, 3])
        grs_inc = int(inc_choice in [1, 3])

        op_val_grs = random.choice(bad_regs if bad_grs else good_regs)

        op_val_grd = random.choice(bad_regs if bad_grd else good_regs)

        op_val = [op_val_grd, op_val_grs, grd_inc, grs_inc]

        prog_insn = ProgInsn(self.insn, op_val, None)

        snippet = ProgSnippet(model.pc, [prog_insn])
        snippet.insert_into_program(program)

        return (snippet, True, model)
