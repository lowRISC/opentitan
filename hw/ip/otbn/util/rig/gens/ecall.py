# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from typing import Optional, Tuple

from shared.insn_yaml import InsnsFile

from ..program import ProgInsn, Program
from ..model import Model
from ..snippet import Snippet
from ..snippet_gen import SnippetGen


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
            size: int,
            model: Model,
            program: Program) -> Optional[Tuple[Snippet, bool, int]]:
        snippet = Snippet([(model.pc, [self.insn])])
        snippet.insert_into_program(program)
        return (snippet, True, 0)

    def pick_weight(self,
                    size: int,
                    model: Model,
                    program: Program) -> float:
        # Choose small weights when size is large and large ones when it's
        # small.
        assert size > 0
        return (1e-10 if size > 5
                else 0.1 if size > 1
                else 1e10)
