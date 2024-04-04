# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import random
from typing import Optional, Tuple

from shared.operand import ImmOperandType, RegOperandType, OperandType

from .loop import Loop
from ..model import Model
from ..program import ProgInsn, Program
from ..snippet import LoopSnippet
from ..snippet_gen import GenCont, GenRet


class BadZeroLoop(Loop):
    '''A snippet generator that generates loops with a zero count'''

    ends_program = True

    def _bad_loop_iterations(self, model: Model) -> Tuple[int, int]:
        '''Like Loop._pick_loop_iterations but always returns 0 iterations'''
        poss_pairs = []
        for idx, value in model.regs_with_known_vals('gpr'):
            if value == 0:
                poss_pairs.append((idx, value))

        # Since x0 contains zero, we'll always have at least one pair.
        assert poss_pairs

        return random.choice(poss_pairs)

    def _bad_loopi_iterations(self) -> Tuple[int, int]:
        '''Like Loop._pick_loopi_iterations but always returns 0 iterations'''
        return (0, 0)

    def _bad_iterations(self,
                        op_type: OperandType,
                        bodysize: int,
                        model: Model) -> Tuple[int, int]:
        '''Like Loop._pick_iterations but always returns 0 iterations'''
        if isinstance(op_type, RegOperandType):
            assert op_type.reg_type == 'gpr'
            return self._bad_loop_iterations(model)
        else:
            assert isinstance(op_type, ImmOperandType)
            return self._bad_loopi_iterations()

    def gen(self,
            cont: GenCont,
            model: Model,
            program: Program) -> Optional[GenRet]:

        model_before = model.copy()

        pieces = self._gen_pieces(cont, model, program)
        if pieces is None:
            return None

        bodysize, good_hd_insn, body_snippet, model, warp = pieces

        # If we successfully generated a loop, generate a new head instruction
        # with the same body size but with zero iterations.
        insn = self.pick_loop_insn()
        op0_type = insn.operands[0].op_type
        op1_type = insn.operands[1].op_type

        iter_opval, num_iters = self._bad_iterations(op0_type,
                                                     bodysize, model_before)

        # Generate a new head instruction
        enc_bodysize = op1_type.op_val_to_enc_val(bodysize, model_before.pc)
        assert enc_bodysize is not None
        bad_hd_insn = ProgInsn(insn, [iter_opval, enc_bodysize], None)

        snippet = LoopSnippet(model_before.pc, bad_hd_insn, body_snippet, None)
        snippet.insert_into_program(program)

        # Return with the initial model (because the head instruction is bad,
        # we'll stop at it)
        return (snippet, model_before)
