# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from typing import Optional

from shared.insn_yaml import InsnsFile

from ..program import ProgInsn, Program
from ..model import Model
from ..snippet import ProgSnippet
from ..snippet_gen import GenCont, GenRet, SnippetGen


class ECall(SnippetGen):
    '''A generator that makes a snippet with a single ECALL instruction'''
    def __init__(self, insns_file: InsnsFile) -> None:
        ecall_insn = self._get_named_insn(insns_file, 'ecall')

        if ecall_insn.operands:
            raise RuntimeError('ECALL instruction in instructions file '
                               'has a nonempty list of operands.')

        if ecall_insn.lsu:
            raise RuntimeError('ECALL instruction in instructions file '
                               'has unexpected LSU information.')

        self.insn = ProgInsn(ecall_insn, [], None)

    def gen(self,
            cont: GenCont,
            model: Model,
            program: Program) -> Optional[GenRet]:
        snippet = ProgSnippet(model.pc, [self.insn])
        snippet.insert_into_program(program)
        return (snippet, None)

    def pick_weight(self,
                    model: Model,
                    program: Program) -> float:
        # Choose small weights when we've got lots of room and large ones when
        # we haven't.
        fuel = model.fuel
        space = program.get_insn_space_left()
        assert fuel > 0
        assert space > 0

        room = min(fuel, space)
        return (1e-10 if room > 5
                else 0.1 if room > 1
                else 1e10)
