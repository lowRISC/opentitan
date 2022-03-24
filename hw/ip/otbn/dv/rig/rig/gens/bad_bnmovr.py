# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import random
from typing import Optional

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
        self.weight = cfg.insn_weights.get(self.insn.mnemonic)

        # Check that the instruction has a positive weight
        if not self.weight:
            self.disabled = True

    def gen(self,
            cont: GenCont,
            model: Model,
            program: Program) -> Optional[GenRet]:

        # Get known registers and split them up as "good" or "bad" depending on
        # whether their values are valid register indices.
        known_regs = model.regs_with_known_vals('gpr')
        bad_regs = []
        good_regs = []
        for reg_idx, reg_val in known_regs:
            if reg_val <= 31:
                good_regs.append(reg_idx)
            else:
                bad_regs.append(reg_idx)

        # We have 4 different options for increments and 4 different options
        # for out of bound register values.
        #
        # For increments, the "inc_choice" variable uses the mapping:
        #
        #    0 => (don't increment anything)
        #    1 => increment grs
        #    2 => increment grd
        #    3 => increment both
        #
        # For register values, we have to pick whether they should be out of
        # bounds or not. "reg_val_choice" follows the mapping:
        #
        #    0 => All in bounds
        #    1 => grs out of bounds
        #    2 => grd out of bounds
        #    3 => both registers out of bounds
        #
        # Concatenate the 2-bit numbers as {reg_val_choice, inc_choice} to get
        # a value between 0 and 15. We want to generate an instruction that
        # will cause an error so either inc_choice has to be 3 (double
        # increment) or reg_val_choice has to be nonzero (at least one
        # out-of-bound register value). These conditions hold iff the combined
        # value is at least 3.
        #
        # bad_regs might be empty. In this case, we can still generate an
        # instruction (note that good_regs will always be nonempty because it
        # contains x0, with a known value of zero). However, this forces
        # reg_val_choice to zero, so we must pick inc_choice = 3.
        choices = 3 if not bad_regs else random.randint(3, 15)

        reg_val_choice = choices // 4
        inc_choice = choices % 4

        bad_grd = reg_val_choice in [2, 3]
        bad_grs = reg_val_choice in [1, 3]

        grd_inc = inc_choice in [2, 3]
        grs_inc = inc_choice in [1, 3]

        op_val_grs = random.choice(bad_regs if bad_grs else good_regs)
        op_val_grd = random.choice(bad_regs if bad_grd else good_regs)

        op_val = [op_val_grd, op_val_grs, int(grd_inc), int(grs_inc)]

        prog_insn = ProgInsn(self.insn, op_val, None)

        snippet = ProgSnippet(model.pc, [prog_insn])
        snippet.insert_into_program(program)

        return (snippet, model)
