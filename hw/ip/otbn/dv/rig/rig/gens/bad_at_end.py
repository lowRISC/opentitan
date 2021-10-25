# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import random
from typing import List, Optional, Tuple

from shared.insn_yaml import InsnsFile

from .branch import Branch
from .jump import Jump
from .loop import Loop
from ..config import Config
from ..program import ProgInsn, Program
from ..model import Model
from ..snippet_gen import GenCont, GenRet


class BadAtEnd(Loop):
    '''A snippet generator that generates a loop/branch/jump at end of a loop

    This works by overriding the _gen_tail method of the Loop generator and
    replacing the last instruction that we would have generated with a loop,
    branch or jump instruction.

    '''

    ends_program = True

    def __init__(self, cfg: Config, insns_file: InsnsFile) -> None:
        super().__init__(cfg, insns_file)
        self.branch_gen = Branch(cfg, insns_file)
        self.jump_gen = Jump(cfg, insns_file)

    def pick_weight(self,
                    model: Model,
                    program: Program) -> float:
        # Only try this if we've got a reasonable amount of room.
        room = min(model.fuel, program.space)
        assert 0 < room
        return (1.0 if room > 50 else 0.0)

    def _gen_tail_insns(self,
                        num_insns: int,
                        model: Model,
                        program: Program) -> Optional[Tuple[List[ProgInsn],
                                                            Model]]:
        assert num_insns > 0
        old_model = model.copy()
        ret = super()._gen_tail_insns(num_insns, model, program)
        if ret is None:
            return None

        insns, model = ret
        assert len(insns) == num_insns

        match_addr = model.pc

        # We need a model to represent the state just before the last
        # instruction. Of course, we can't "unwind" the state update that we
        # just did. However, a merge between the initial state and the end
        # state gives a sound (if very imprecise!) approximation.
        #
        # Since the Model.merge() method expects the two models to have the
        # same PC (which is the usual situation when implementing phi nodes),
        # we also have to teleport both models to the right place.
        model.pc -= 4
        old_model.pc = model.pc
        model.merge(old_model)

        # Pick a new instruction to replace the last one we generated. Start by
        # shuffling the numbers from 0..2, which will represent Branch, Loop,
        # Jump respectively. The idea is that we want to try them in an
        # arbitrary order, but don't want to fail completely if one of the
        # other generators might have worked.
        types = list(range(3))
        random.shuffle(types)
        for lbj in types:
            if lbj == 0:
                # Loop! Pick an loop head (with an arbitrary "100" for
                # space_here and without setting up program properly: it
                # doesn't really matter). Pass False as the "check" argument:
                # we don't want to check anything about whether the implied
                # loop overlaps with existing code.
                retL = self._pick_head(100, False, model, program)
                if retL is not None:
                    tail_insn, _ = retL
                    break
            elif lbj == 1:
                # Branch!
                retB = self.branch_gen.gen_head(model, program)
                if retB is not None:
                    tail_insn, _ = retB
                    break
            else:
                assert lbj == 2
                # Jump!

                # The merge() function above took the minimum of the two
                # models' amount of fuel. Since Jump.gen_tgt() updates the
                # model with the new instruction, we need to give it one extra
                # fuel (to match what got incorrectly subtracted for the
                # instruction we're replacing). It also adds the generated
                # instruction to the program: we don't want that, so we give it
                # a throw-away copy to modify.
                model.fuel += 1

                retJ = self.jump_gen.gen_tgt(model, program.copy(), None)
                if retJ is not None:
                    tail_insn, _, _ = retJ

        if tail_insn is None:
            return

        # Fix up model.pc. The "head" generators for loop and branch don't
        # update the model for what they've generated, so we'll be 4 bytes too
        # early. Jump.gen_tgt() updates the model to match, so we'll be at some
        # crazy new location! It doesn't really matter (we're faulting anyway),
        # but Loop expects us to leave model.pc in the right place, so we need
        # to fix it up here.
        model.pc = match_addr

        insns[-1] = tail_insn
        return (insns, model)

    def gen(self,
            cont: GenCont,
            model: Model,
            program: Program) -> Optional[GenRet]:
        # Run the Loop generator, but with our _gen_tail, which means we'll put
        # an unexpected jump/branch/loop at the end of the body.
        ret = super().gen(cont, model, program)
        if ret is None:
            return None

        # If the Loop generator returned success, that's great! However, we
        # need to fix things up a bit for the changes we've made. Specifically,
        # the "done" flag should be true (since this is supposed to cause a
        # fault) and the final PC should be 4 less, pointing just before the
        # last instruction in the loop.
        snippet, model = ret

        model.pc -= 4
        return (snippet, model)
