# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import random
from typing import Optional, List, Tuple

from ..model import Model
from ..program import ProgInsn, Program

from shared.insn_yaml import Insn, InsnsFile
from ..snippet import ProgSnippet
from ..snippet_gen import GenCont, GenRet, SnippetGen
from ..config import Config


class BranchGen(SnippetGen):
    ''' A snippet generator base class to generate bad or untaken BEQ and BNE.

    BadBranch and UntakenBranch inherit this class.

    '''

    def __init__(self, cfg: Config, insns_file: InsnsFile) -> None:
        super().__init__()

        self.insns = []
        self.weights = []

        self.beq = self._get_named_insn(insns_file, 'beq')
        self.bne = self._get_named_insn(insns_file, 'bne')

        self.imm_op_type = self.bne.operands[2].op_type

        for insn in insns_file.insns:
            if insn.mnemonic in ['beq', 'bne']:
                weight = cfg.insn_weights.get(insn.mnemonic)
                if weight > 0:
                    self.weights.append(weight)
                    self.insns.append(insn)

        # Disable this generator if no branch instruction has a positive weight
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
        assert known_regs

        # Pick a random register among known registers.
        idx, value = random.choice(known_regs)

        # Get the chosen base register index as grs1 and grs2 operand. This is
        # because we want to branch to the faulty addresses with this snippet.
        op_val_grs1 = idx
        assert op_val_grs1 is not None

        equals = []
        not_equals = []

        for reg_idx, reg_val in known_regs:
            if reg_val == value:
                equals.append(reg_idx)
            else:
                not_equals.append(reg_idx)
        # Pick the offset address
        tgt_addr = self.pick_offset(min_addr, max_addr, model, program)
        off_enc = self.imm_op_type.op_val_to_enc_val(tgt_addr, model.pc)
        assert off_enc is not None

        # Pick the instruction and second operand
        ret = self.pick_second_op(equals, not_equals)
        if ret is None:
            return None
        op_val_grs2, chosen_insn = ret
        op_vals = [op_val_grs1, op_val_grs2, off_enc]

        prog_insn = ProgInsn(chosen_insn, op_vals, None)
        snippet = ProgSnippet(model.pc, [prog_insn])
        snippet.insert_into_program(program)

        self.update_for_insn(model, prog_insn)

        return (snippet, model)

    def pick_offset(self,
                    min_addr: int,
                    max_addr: int,
                    model: Model,
                    program: Program) -> int:
        raise NotImplementedError()

    def pick_second_op(self,
                       equals: List[int],
                       not_equals: List[int]) -> Optional[Tuple[int, Insn]]:
        raise NotImplementedError()

    def update_for_insn(self,
                        model: Model,
                        prog_insn: ProgInsn) -> None:
        return None
