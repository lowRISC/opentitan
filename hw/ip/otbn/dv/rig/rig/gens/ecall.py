# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from typing import Optional

from shared.insn_yaml import InsnsFile

from ..config import Config
from ..program import ProgInsn, Program
from ..model import Model
from ..snippet import ProgSnippet, Snippet
from ..snippet_gen import GenCont, GenRet, SnippetGen


class ECall(SnippetGen):
    '''A generator that makes a snippet with a single ECALL instruction'''
    def __init__(self, cfg: Config, insns_file: InsnsFile) -> None:
        super().__init__()

        ecall_insn = self._get_named_insn(insns_file, 'ecall')

        if ecall_insn.operands:
            raise RuntimeError('ECALL instruction in instructions file '
                               'has a nonempty list of operands.')

        if ecall_insn.lsu:
            raise RuntimeError('ECALL instruction in instructions file '
                               'has unexpected LSU information.')

        self.insn = ProgInsn(ecall_insn, [], None)

        if cfg.insn_weights.values.get('ecall') is not None:
            raise ValueError('Config at {} configures the instruction '
                             'weight of ECALL. This has no effect: configure '
                             'the weight of the ECall generator instead.'
                             .format(cfg.path))

    def gen_at(self, pc: int, program: Program) -> Snippet:
        '''Generate an ECALL instruction at pc and insert into program'''
        snippet = ProgSnippet(pc, [self.insn])
        snippet.insert_into_program(program)
        return snippet

    def gen(self,
            cont: GenCont,
            model: Model,
            program: Program) -> Optional[GenRet]:
        return (self.gen_at(model.pc, program), None)

    def pick_weight(self,
                    model: Model,
                    program: Program) -> float:
        # Choose small weights when we've got lots of room and large ones when
        # we haven't.
        room = min(model.fuel, program.space)
        assert 0 < room
        return (1e-10 if room > 5
                else 0.1 if room > 1
                else 1e10)
