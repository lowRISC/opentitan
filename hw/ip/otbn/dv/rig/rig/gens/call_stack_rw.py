# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import random
from typing import Optional

from shared.insn_yaml import InsnsFile
from shared.operand import RegOperandType

from ..config import Config
from ..program import ProgInsn, Program
from ..model import Model
from ..snippet import ProgSnippet
from ..snippet_gen import GenCont, GenRet, SnippetGen


class CallStackRW(SnippetGen):
    '''A snippet generator that tries to exercise the call stack

    We already have code that can exercise the call stack (e.g.
    StraightLineInsn), but there are certain things that it will never do (pop
    & push when the stack is full, for example) and other multiple uses of x1
    aren't particularly frequent. Generate more here!

    '''

    def __init__(self, cfg: Config, insns_file: InsnsFile) -> None:
        super().__init__()

        # Grab instructions like "add" or "sub", which take two GPRs as inputs
        # and write one GPR as an output.
        self.insns = []
        self.indices = []
        self.weights = []

        for insn in insns_file.insns:
            gpr_dsts = []
            gpr_srcs = []

            for idx, op in enumerate(insn.operands):
                if not isinstance(op.op_type, RegOperandType):
                    continue
                is_gpr = op.op_type.reg_type == 'gpr'
                is_dst = op.op_type.is_dest()

                if is_gpr:
                    if is_dst:
                        gpr_dsts.append(idx)
                    else:
                        gpr_srcs.append(idx)

            if len(gpr_dsts) == 1 and len(gpr_srcs) == 2 and insn.lsu is None:
                weight = cfg.insn_weights.get(insn.mnemonic)
                if weight > 0:
                    self.insns.append(insn)
                    self.indices.append((gpr_dsts[0], gpr_srcs[0], gpr_srcs[1]))
                    self.weights.append(weight)

        if not self.insns:
            # All the weights for the instructions we can use are zero
            self.disabled = True

    def gen(self,
            cont: GenCont,
            model: Model,
            program: Program) -> Optional[GenRet]:
        # We can't read or write x1 when it's marked const.
        if model.is_const('gpr', 1):
            return None

        # Make sure we don't get paint ourselves into a corner
        if program.get_insn_space_at(model.pc) <= 1:
            return None

        # Pick an instruction
        idx = random.choices(range(len(self.weights)), weights=self.weights)[0]
        grd_idx, grs1_idx, grs2_idx = self.indices[idx]
        insn = self.insns[idx]

        # This instruction will have one GPR dest and two GPR sources. It might
        # also have some immediate values. Decide how to fill it out.
        # Interesting patterns are
        #
        #  (0)  add   x1, x1, ??
        #  (1)  add   x1, ??, x1
        #  (2)  add   x1, x1, x1
        #  (3)  add   ??, x1, x1
        #  (4)  add   x1, ??, ??
        #
        # We can generate any of 0-3 as long as the call stack is nonempty
        # (which we've already guaranteed with pick_weight). We can generate 4
        # if the stack is not full.
        min_idx = 4 if model.call_stack.empty() else 0
        max_idx = 3 if model.call_stack.full() else 4
        if min_idx > max_idx:
            # This is possible (call stack both empty and full) because we
            # might not have full knowledge of the state of the call stack.
            return None

        flavour = random.randint(min_idx, max_idx)
        x1_grd = flavour != 3
        x1_grs1 = flavour not in [1, 4]
        x1_grs2 = flavour not in [0, 4]

        op_vals = []
        for idx, operand in enumerate(insn.operands):
            use_x1 = ((x1_grd and idx == grd_idx) or
                      (x1_grs1 and idx == grs1_idx) or
                      (x1_grs2 and idx == grs2_idx))
            if use_x1:
                op_vals.append(1)
            else:
                # Make sure we don't use x1 when we're not expecting to
                if not isinstance(operand.op_type, RegOperandType):
                    weights = None
                else:
                    weights = {1: 0.0}

                enc_op_val = model.pick_operand_value(operand.op_type, weights)
                if enc_op_val is None:
                    return None
                op_vals.append(enc_op_val)

        prog_insn = ProgInsn(insn, op_vals, None)
        snippet = ProgSnippet(model.pc, [prog_insn])
        snippet.insert_into_program(program)

        model.update_for_insn(prog_insn)
        model.pc += 4

        return (snippet, False, model)
