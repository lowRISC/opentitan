# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import random
from typing import Optional, Tuple

from shared.insn_yaml import InsnsFile
from shared.operand import ImmOperandType

from ..config import Config
from ..program import ProgInsn, Program
from ..model import Model
from ..snippet import ProgSnippet
from ..snippet_gen import GenCont, GenRet, SnippetGen
from .straight_line_insn import StraightLineInsn


class BadIspr(SnippetGen):
    '''A snippet to generate accesses to invalid CSRs/WSRs'''

    ends_program = True

    def __init__(self, cfg: Config, insns_file: InsnsFile) -> None:
        super().__init__()

        self.insns = []
        self.weights = []
        self.straightgen = StraightLineInsn(cfg, insns_file)

        for insn in insns_file.insns:
            # Pick only the instructions pertaining to CSR and WSR.
            if insn.mnemonic not in ['csrrw', 'csrrs', 'wsrs', 'wsrw']:
                continue

            assert not (insn.python_pseudo_op or insn.literal_pseudo_op)

            # The instructions we're interested in are all straight-line
            assert insn.straight_line

            weight = cfg.insn_weights.get(insn.mnemonic)
            if weight > 0:
                self.insns.append(insn)
                self.weights.append(weight)

        # Disable the generator if no instruction has a positive weight
        assert len(self.insns) == len(self.weights)
        if not self.insns:
            self.disabled = True

    def gen(self,
            cont: GenCont,
            model: Model,
            program: Program) -> Optional[GenRet]:
        pc = model.pc
        ret = self._gen(model, program)
        if ret is None:
            return None

        prog_insn, model = ret
        snippet = ProgSnippet(pc, [prog_insn])
        snippet.insert_into_program(program)

        return (snippet, model)

    def _gen(self,
             model: Model,
             program: Program) -> Optional[Tuple[ProgInsn, Model]]:

        weights = self.weights
        prog_insn = None
        while prog_insn is None:
            idx = random.choices(range(len(self.insns)), weights=weights)[0]

            # weights[idx] will be positive so long as at least one instruction
            # has positive weight. If it's zero, it means that every weight is
            # zero and we should give up.
            if weights[idx] < 0:
                return None

            # Try to fill out the instruction. On failure, clear the weight for
            # this index and go around again. We take the copy here, rather
            # than outside the loop, because we don't expect this to happen
            # very often.
            prog_insn = self.straightgen.fill_insn(self.insns[idx], model)

            if prog_insn is None:
                weights = self.weights.copy()
                weights[idx] = 0
                continue

            assert prog_insn.lsu_info is not None
            mem_type, tgt_addr = prog_insn.lsu_info
            # Replace good CSR / WSR address with bad address.
            bad_addr = model.pick_bad_addr(mem_type)
            assert bad_addr is not None
            prog_insn.lsu_info = mem_type, bad_addr
            imm_idx = None
            for i, each in enumerate(prog_insn.insn.operands):
                if isinstance(each.op_type, ImmOperandType):
                    assert imm_idx is None
                    imm_idx = i
            assert imm_idx is not None
            prog_insn.operands[imm_idx] = bad_addr

            # In the case of a randomly generated CSRRW, it is better to have
            # UNIMP instead of a write to a random address since it is actually
            # an instruction alias.
            if self.insns[idx].mnemonic == "csrrw" and random.random() < 0.8:
                # UNIMP instruction is equivalent to CSRRW x0, 0xC00, x0
                prog_insn.operands = [0, 0xC00, 0]

        return (prog_insn, model)
