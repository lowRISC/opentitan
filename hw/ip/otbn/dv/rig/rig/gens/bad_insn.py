# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import random
from typing import Optional

from shared.insn_yaml import InsnsFile

from ..config import Config
from ..program import DummyProgInsn, Program
from ..model import Model
from ..snippet import ProgSnippet
from ..snippet_gen import GenCont, GenRet, SnippetGen


class BadInsn(SnippetGen):
    '''A simple snippet generator that generates one invalid instruction'''

    ends_program = True

    def __init__(self, cfg: Config, insns_file: InsnsFile) -> None:
        super().__init__()

        # Take a copy of the instructions file: we'll need it when generating
        # random data in order to make sure we generate junk.
        self.insns_file = insns_file

    def _get_badbits(self) -> int:
        for _ in range(50):
            data = random.getrandbits(32)
            # Is this (by fluke) actually a valid instruction? It's not very
            # likely, but we need to check that it isn't.
            if self.insns_file.mnem_for_word(data) is None:
                return data

        # Since the encoding density isn't all that high (< 25%), the chances
        # of getting here are vanishingly small (should be < 2^100). Just
        # assert that it doesn't happen.
        assert 0

    def gen(self,
            cont: GenCont,
            model: Model,
            program: Program) -> Optional[GenRet]:
        prog_insn = DummyProgInsn(self._get_badbits())
        snippet = ProgSnippet(model.pc, [prog_insn])
        snippet.insert_into_program(program)
        return (snippet, model)

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
