# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import random
from typing import Optional

from shared.insn_yaml import InsnsFile

from .loop import Loop
from ..config import Config
from ..model import Model
from ..program import ProgInsn, Program
from ..snippet import LoopSnippet
from ..snippet_gen import GenCont, GenRet


class BadGiantLoop(Loop):
    '''A generator for loops with end addresses that don't lie in memory

    This generator has "ends_program = True", but doesn't end the program in
    itself. Instead, it sets up a loop with an endpoint that doesn't fit in
    memory (so the loop body will never actually terminate) and then generates
    a sequence for the rest of the program, to go inside the body. OTBN will
    complete its operation without popping the loop off the stack.

    '''

    ends_program = True

    def __init__(self, cfg: Config, insns_file: InsnsFile) -> None:
        super().__init__(cfg, insns_file)

    def gen(self,
            cont: GenCont,
            model: Model,
            program: Program) -> Optional[GenRet]:

        # We need space for at least 2 instructions here: one for the loop head
        # instruction and one for the minimal body (which might contain an
        # ECALL, for example)
        space_here = program.get_insn_space_at(model.pc)
        if space_here < 2:
            return None

        # Similarly, the smallest possible loop will take 2 instructions
        if program.space < 2:
            return None

        # And we don't want to overflow the loop stack
        if model.loop_stack.maybe_full():
            return None

        insn = self.pick_loop_insn()
        iters_op_type = insn.operands[0].op_type
        bodysize_op_type = insn.operands[1].op_type

        bodysize_range = bodysize_op_type.get_op_val_range(model.pc)
        assert bodysize_range is not None

        bodysize_min, bodysize_max = bodysize_range

        # Adjust bodysize_min to make sure we pick an end address that's larger
        # than IMEM (and check that we can represent the result).
        bodysize_min = max(bodysize_min, (program.imem_size - model.pc) // 4)
        if bodysize_max < bodysize_min:
            return None

        # Pick bodysize, preferring the endpoints
        x = random.random()
        if x < 0.4:
            bodysize = bodysize_min
        elif x < 0.8:
            bodysize = bodysize_max
        else:
            bodysize = random.randint(bodysize_min, bodysize_max)

        enc_bodysize = bodysize_op_type.op_val_to_enc_val(bodysize, model.pc)
        assert enc_bodysize is not None

        # Now pick the number of iterations (not that the number actually
        # matters). Note that we ignore any warp specified: since we'll never
        # actually complete a loop iteration, there's not much point specifying
        # any loop warping.
        iters = self.pick_iterations(iters_op_type, bodysize, model)
        if iters is None:
            return None

        iters_opval, num_iters, warp = iters
        hd_addr = model.pc
        hd_insn = ProgInsn(insn, [iters_opval, enc_bodysize], None)

        end_addr = model.pc + 4 * bodysize

        body_model, body_loop_stack = self._setup_body(hd_insn, end_addr,
                                                       model, program, False)
        assert body_loop_stack is None

        # At this point, all the "loop related work" is done: we've entered the
        # loop body (from which we can never leave). Now call the continuation
        # with a flag to say that we'd like the generation to complete.
        body_snippet, end_model = cont(body_model, program, True)

        # Because we passed end=True to cont, the snippet from the continuation
        # is not None.
        assert body_snippet is not None

        loop_snippet = LoopSnippet(hd_addr, hd_insn, body_snippet, None)
        return (loop_snippet, end_model)
