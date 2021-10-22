# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import random
from typing import Optional, List, Tuple

from ..model import Model
from ..program import ProgInsn, Program

from .branch_gen import BranchGen
from shared.insn_yaml import Insn
from ..snippet_gen import GenCont, GenRet


class UntakenBranch(BranchGen):
    '''A snippet generator for branches that are not taken.'''

    def gen(self,
            cont: GenCont,
            model: Model,
            program: Program) -> Optional[GenRet]:
        # Return None if this is the last instruction in the current gap
        # because we need to either jump or do an ECALL to avoid getting stuck.
        if program.get_insn_space_at(model.pc) <= 1:
            return None
        return super().gen(cont, model, program)

    def pick_offset(self,
                    min_addr: int,
                    max_addr: int,
                    model: Model,
                    program: Program) -> int:

        # The below code picks up aligned and unaligned addresses randomly with
        # 50% probability.
        tgt_addr = random.randrange(min_addr, max_addr + 1, 2)

        return tgt_addr

    def pick_second_op(self,
                       equals: List[int],
                       not_equals: List[int]) -> Optional[Tuple[int, Insn]]:
        if not_equals:
            chosen_insn = random.choices(self.insns, weights=self.weights)[0]
        else:
            chosen_insn = self.bne
            bne_weight = self.weights[0]
            if not bne_weight:
                return None

        # Generates instructions having registers with unequal values for beq
        # and registers with equal values for bne.
        grs2_choices = not_equals if chosen_insn.mnemonic == 'beq' else equals
        assert grs2_choices

        op_val_grs2 = random.choice(grs2_choices)

        return (op_val_grs2, chosen_insn)

    def update_for_insn(self,
                        model: Model,
                        prog_insn: ProgInsn) -> None:
        model.update_for_insn(prog_insn)
        model.pc += 4
