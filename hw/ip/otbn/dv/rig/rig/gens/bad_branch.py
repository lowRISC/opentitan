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


class BadBranch(SnippetGen):
    '''A snippet generator that generates program ending branch instructions.

    This includes out of bounds branches in negative and positive extremes

    '''

    ends_program = True

    def __init__(self, cfg: Config, insns_file: InsnsFile) -> None:
        super().__init__()

        self.insns = []
        self.weights = []

        self.beq = self._get_named_insn(insns_file, 'beq')
        self.bne = self._get_named_insn(insns_file, 'bne')

        # beq and bne expect operands: grs1, grs2, offset
        for insn in [self.beq, self.bne]:
            if not (len(insn.operands) == 3 and
                    isinstance(insn.operands[0].op_type, RegOperandType) and
                    insn.operands[0].op_type.reg_type == 'gpr' and
                    not insn.operands[0].op_type.is_dest() and
                    isinstance(insn.operands[1].op_type, RegOperandType) and
                    insn.operands[1].op_type.reg_type == 'gpr' and
                    not insn.operands[1].op_type.is_dest() and
                    isinstance(insn.operands[2].op_type, ImmOperandType) and
                    insn.operands[2].op_type.signed):
                raise RuntimeError('{} instruction from instructions file is not '
                                   'the shape expected by the Branch generator.'
                                   .format(insn.mnemonic))

        self.imm_op_type = self.bne.operands[2].op_type

        for insn in insns_file.insns:
            if insn.mnemonic in ['beq', 'bne']:
                weight = cfg.insn_weights.get(insn.mnemonic)
                if weight > 0:
                    self.weights.append(weight)
                    self.insns.append(insn)

        # Check that at least one instruction has a positive weight.
        assert len(self.insns) == len(self.weights)
        if not self.weights:
            self.disabled = True

    def gen(self,
            cont: GenCont,
            model: Model,
            program: Program) -> Optional[GenRet]:

        # Pick maximum and minimum address range for the current PC.
        imm_rng = self.imm_op_type.get_op_val_range(model.pc)
        assert imm_rng is not None

        min_addr, max_addr = imm_rng

        # Get known registers. We always have x0.
        # So it should never fail.
        known_regs = model.regs_with_known_vals('gpr')
        assert known_regs is not None

        # Pick a random register among known registers.
        idx, value = random.choice(known_regs)

        equals = []
        not_equals = []

        for reg_idx, reg_val in known_regs:
            if reg_val == value:
                equals.append(reg_idx)
            else:
                not_equals.append(reg_idx)

        # Get the chosen base register index as grs1 and grs2 operand. This is
        # because we want to branch to the faulty addresses with this snippet.
        op_val_grs1 = idx
        assert op_val_grs1 is not None

        # We need to pick an out of bounds offset from all available values (A)
        # mode is a random variable to ensure that all the bins are hit
        # for offset range. It gives equal weight to all address ranges.

        mode = random.randint(0, 4)
        if mode == 0 and min_addr <= -4:
            tgt_addr = random.randrange(min_addr, -4, 4)
        elif mode <= 1 and program.imem_size <= max_addr:
            tgt_addr = random.randrange(program.imem_size, max_addr, 4)
        elif mode <= 2 and min_addr <= -4:
            tgt_addr = min_addr
        elif mode <= 3 and program.imem_size <= max_addr:
            tgt_addr = max_addr
        else:
            assert mode <= 4
            tgt_addr = random.randrange(min_addr + 2, max_addr, 4)
        off_enc = self.imm_op_type.op_val_to_enc_val(tgt_addr, model.pc)

        assert off_enc is not None

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

        op_vals = [op_val_grs1, op_val_grs2, off_enc]

        prog_insn = ProgInsn(chosen_insn, op_vals, None)

        snippet = ProgSnippet(model.pc, [prog_insn])
        snippet.insert_into_program(program)

        return (snippet, True, model)
