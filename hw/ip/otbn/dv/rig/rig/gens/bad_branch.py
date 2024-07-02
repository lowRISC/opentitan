# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import random
from typing import Optional, List, Tuple

from ..model import Model
from ..program import Program
from shared.insn_yaml import Insn

from .branch_gen import BranchGen


class BadBranch(BranchGen):
    '''A snippet generator that generates program ending branch instructions.

    This includes out of bounds branches in negative and positive extremes

    '''

    ends_program = True

    def pick_offset(self,
                    min_addr: int,
                    max_addr: int,
                    model: Model,
                    program: Program) -> int:

        # We only want to pick values that we can actually encode as a 12-bit
        # signed differences from the current PC (shifted left by 1).
        min_addr = max(min_addr, model.pc - 4096)
        max_addr = min(max_addr, model.pc + 4094)

        # Check that there are still any encodable address. (This will fail if
        # the initial call had e.g. min_addr and max_addr were enormous and
        # model.pc=0)
        assert min_addr <= max_addr

        # We need to pick an out of bounds offset from all available values (A)
        # mode is a random variable to ensure that all the bins are hit
        # for offset range. It gives equal weight to all address ranges.
        mode = random.randint(0, 4)
        if mode == 0 and min_addr <= -4:
            tgt_addr = random.randrange(min_addr, -4 + 1, 4)
        elif mode <= 1 and program.imem_size <= max_addr:
            tgt_addr = random.randrange(program.imem_size, max_addr + 1, 4)
        elif mode <= 2 and min_addr <= -4:
            tgt_addr = min_addr
        elif mode <= 3 and program.imem_size - 1 <= max_addr:
            tgt_addr = max_addr
        elif mode <= 4 and program.imem_size - 1 <= max_addr:
            tgt_addr = random.randrange(max(0, min_addr),
                                        min(program.imem_size, max_addr - 4),
                                        4) + 2
        else:
            assert mode <= 4
            tgt_addr = random.randrange(min_addr + 2, max_addr + 1, 4)

        return tgt_addr

    def pick_second_op(self,
                       equals: List[int],
                       not_equals: List[int]) -> Optional[Tuple[int, Insn]]:
        # Pick the instruction from the weighted list.
        if not_equals:
            chosen_insn = random.choices(self.insns, weights=self.weights)[0]
        else:
            chosen_insn = self.beq
            beq_weight = self.weights[0]
            if not beq_weight:
                return None

        grs2_choices = equals if chosen_insn.mnemonic == 'beq' else not_equals
        assert grs2_choices

        op_val_grs2 = random.choice(grs2_choices)
        assert op_val_grs2 is not None

        return (op_val_grs2, chosen_insn)
