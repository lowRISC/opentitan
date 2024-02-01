# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from typing import List, Optional, Tuple

from shared.insn_yaml import InsnsFile
from shared.operand import ImmOperandType, OperandType

from .loop import Loop
from ..config import Config
from ..program import ProgInsn, Program
from ..model import Model
from ..snippet import Snippet
from ..snippet_gen import GenCont, GenRet


class LoopDupEndInner(Loop):
    '''The generator used by LoopDupEnd to make the inner loop'''
    def __init__(self, cfg: Config, insns_file: InsnsFile) -> None:
        super().__init__(cfg, insns_file)
        self.loop_end_stack = []  # type: List[int]

    def gen_with_end(self,
                     loop_end: int,
                     cont: GenCont,
                     model: Model,
                     program: Program) -> Optional[GenRet]:
        self.loop_end_stack.append(loop_end)
        try:
            return self.gen(cont, model, program)
        finally:
            assert self.loop_end_stack[-1] == loop_end
            self.loop_end_stack.pop()

    def _pick_loop_shape(self,
                         op0_type: OperandType,
                         op1_type: ImmOperandType,
                         space_here: int,
                         check: bool,
                         model: Model,
                         program: Program) -> Optional[Loop.Shape]:
        assert self.loop_end_stack
        loop_end = self.loop_end_stack[-1]

        assert model.pc < loop_end
        bodysize = (loop_end - model.pc) // 4
        if check:
            tail_pc = model.pc + 4 * bodysize
            assert program.get_insn_space_at(tail_pc) >= 2

        iters = self.pick_iterations(op0_type, bodysize, model)
        if iters is None:
            return None

        return (bodysize, iters)


class LoopDupEnd(Loop):
    '''A generator for two nested loops sharing an end address.

    This generator makes the outer loop, using an instance of LoopDupEndInner
    to make the inner one.

    Such a loop nesting is bad news in normal operation: we'll never be able to
    pop off the rest of the loop stack. But we've got some coverage points for
    this happening, so we need to be able to generate it. Note that, unlike
    most "bad behaviour" generators, this doesn't set the ends_program flag:
    OTBN won't spot any error, we'll just use up some of the loop stack.

    '''
    def __init__(self, cfg: Config, insns_file: InsnsFile) -> None:
        super().__init__(cfg, insns_file)
        self.inner_gen = LoopDupEndInner(cfg, insns_file)

        # The stack of loop ends and continuations
        self.stack = []  # type: List[Tuple[int, GenCont]]

    def pick_weight(self,
                    model: Model,
                    program: Program) -> float:
        # Pick a weight that decreases with current loop depth. Once the
        # generated code has run, we lose access to all existing loops, so we'd
        # probably rather not run it when deeply nested.
        return 1 / (1 << model.loop_stack.max_depth())

    def _gen_body(self,
                  bodysize: int,
                  single_iter: bool,
                  bogus_insn: ProgInsn,
                  cont: GenCont,
                  model: Model,
                  program: Program) -> Optional[GenRet]:
        loop_end = model.pc + 4 * (bodysize - 1)
        cont = cont
        self.stack.append((loop_end, cont))
        try:
            return super()._gen_body(bodysize, single_iter,
                                     bogus_insn, cont, model, program)
        finally:
            assert self.stack[-1] == (loop_end, cont)
            self.stack.pop()

    def _gen_tail(self,
                  num_insns: int,
                  model: Model,
                  program: Program) -> Optional[Tuple[Snippet, Model]]:
        # Overriden from base class. The Loop generator derives a loop body as
        # some (possibly empty) free-form "head" part, followed by a sled of
        # straight-line instructions. Here, we override the "sled generation"
        # and insert another loop, carefully crafted to collide with the end
        # address.

        # Since we need at least two instructions for a loop and loop body,
        # give up if num_insns is 1.
        assert 0 <= num_insns
        if num_insns == 1:
            return None

        # The loop end and continuation were grabbed by _gen_body.
        assert self.stack
        loop_end, cont = self.stack[-1]
        ret = self.inner_gen.gen_with_end(loop_end, cont, model, program)
        if ret is None:
            return None

        snippet, model = ret

        # Add a bogus extra copy of the loop end address to model's loop stack
        # here. Then Loop's _gen_body implementation will pop the top one off,
        # getting to the state that OTBN is actually in (where we've popped one
        # already, but can't pop the second).
        model.loop_stack.push(loop_end)

        return (snippet, model)
