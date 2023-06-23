# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import random
from typing import Optional, Tuple

from shared.insn_yaml import Insn, InsnsFile
from shared.operand import ImmOperandType, RegOperandType, OperandType

from .jump import Jump
from .loop import Loop
from ..config import Config
from ..program import ProgInsn, Program
from ..model import LoopStack, Model
from ..snippet import LoopSnippet, ProgSnippet, Snippet
from ..snippet_gen import GenCont, GenRet, SnippetGen


class BadDeepLoop(SnippetGen):
    '''A snippet generator that generates loops to overflow the stack'''

    ends_program = True

    def __init__(self, cfg: Config, insns_file: InsnsFile) -> None:
        super().__init__()
        self.jump_gen = Jump(cfg, insns_file)
        self.loop_gen = Loop(cfg, insns_file)

    def pick_weight(self,
                    model: Model,
                    program: Program) -> float:
        # Only try this if we've got a reasonable amount of room.
        room = min(model.fuel, program.space)
        assert 0 < room
        return (1.0 if room > 50 else 0.0)

    def _pick_bodysize(self,
                       insn: Insn,
                       pc: int,
                       program: Program) -> Tuple[int, int]:
        '''Pick the size of the loop body.

        Returns (enc_bodysize, end_addr).

        '''
        # Pick some value for bodysize that either points at an existing
        # instruction or points above the top of memory. Rather than doing
        # something clever, we pick the address at random and "re-roll" if it
        # points at a gap in instruction memory. Since bodysize_range[1] is
        # 4096, giving a maximum address of 16KiB, which happens to equal the
        # size of IMEM, we know it's going to be possible. Try to pick 50
        # times, which should fail with probability at most 1/4^50 = 1/2^100.
        bodysize_op_type = insn.operands[1].op_type
        bodysize_range = bodysize_op_type.get_op_val_range(pc)
        assert bodysize_range is not None

        bodysize = None
        for _ in range(50):
            guess = random.randint(bodysize_range[0], bodysize_range[1])
            last_insn_addr = pc + 4 * guess
            if ((last_insn_addr >= program.imem_size or
                 program.get_insn_space_at(last_insn_addr) == 0)):
                bodysize = guess
                break

        assert bodysize is not None
        enc_bodysize = bodysize_op_type.op_val_to_enc_val(bodysize, pc)
        assert enc_bodysize is not None
        return (enc_bodysize, pc + 4 * guess)

    def _pick_loop_iterations(self, model: Model) -> Optional[int]:
        # This is like Loop._pick_loop_iterations, but doesn't try to weight
        # towards small counts (since we know we're only doing it once anyway)
        poss_pairs = [(idx, value)
                      for idx, value in model.regs_with_known_vals('gpr')
                      if value > 0]
        if not poss_pairs:
            return None
        return random.choice(poss_pairs)[0]

    def _pick_loopi_iterations(self, op_type: OperandType, pc: int) -> int:
        # Like Loop._pick_loopi_iterations but simpler because it doesn't try
        # to weight towards small counts.
        assert isinstance(op_type, ImmOperandType)
        iters_range = op_type.get_op_val_range(pc)
        assert iters_range is not None
        iters_lo, iters_hi = iters_range
        assert 1 <= iters_hi
        num_iters = random.randint(max(iters_lo, 1), iters_hi)

        enc_val = op_type.op_val_to_enc_val(num_iters, pc)
        assert enc_val is not None
        return enc_val

    def _gen_loop_head(self,
                       model: Model,
                       program: Program) -> Tuple[ProgInsn, int]:
        '''Generate a LOOP or LOOPI instruction

        Returns (hd_insn, end_address).

        '''

        # Pick an instruction (LOOP vs. LOOPI) and number of iterations
        # together. This means that if we've only got GPRs equal to zero (an
        # invalid loop count), we can still guarantee to pick something
        # sucessfully.
        insn = self.loop_gen.pick_loop_insn()
        iters_op_type = insn.operands[0].op_type
        enc_iters = None
        if isinstance(iters_op_type, RegOperandType):
            assert iters_op_type.reg_type == 'gpr'
            enc_iters = self._pick_loop_iterations(model)
            if enc_iters is None:
                insn = self.loop_gen.loopi
                iters_op_type = insn.operands[0].op_type
        if enc_iters is None:
            assert insn is self.loop_gen.loopi
            enc_iters = self._pick_loopi_iterations(iters_op_type, model.pc)

        enc_bodysize, end_addr = self._pick_bodysize(insn, model.pc, program)

        return (ProgInsn(insn, [enc_iters, enc_bodysize], None), end_addr)

    def _gen_loop_stack(self,
                        model: Model,
                        program: Program) -> Tuple[Snippet, Model]:
        '''Generate stack of loop instructions, returning snippet and new model

        This also inserts the instructions into program.

        '''
        space_here = program.get_insn_space_at(model.pc)
        # space_here should always be positive (otherwise we got stuck already)
        assert space_here >= 1

        # We should only have run if we knew the exact loop depth
        assert model.loop_stack.min_depth() == model.loop_stack.max_depth()

        if model.loop_stack.maybe_full():
            # We've bottomed out. Store the model (which we already copied
            # above)
            prog_insn, _ = self._gen_loop_head(model, program)

            # Note that we generate a ProgSnippet, not a LoopSnippet here:
            # while we've got a loop instruction, we happen to know that it
            # will fault, so it's going to behave more like a straight line
            # instruction. Also, we don't have a snippet for the body so the
            # types don't really work for LoopSnippet.
            snippet = ProgSnippet(model.pc, [prog_insn])
            snippet.insert_into_program(program)

            # Note that we don't update model for this instruction: we know
            # that it will cause an error, so we want to leave PC pointing at
            # it (not just after).

            return (snippet, model)

        # Our space calculations in gen() should have ensured that this is
        # true.
        assert space_here >= 2

        hd_pc = model.pc
        hd_insn, end_addr = self._gen_loop_head(model, program)
        program.add_insns(hd_pc, [hd_insn])
        model.update_for_insn(hd_insn)
        model.pc += 4
        model.loop_stack.push(end_addr)

        body_snippet = None  # type: Optional[Snippet]

        if space_here <= 2:
            # If we've run out of space in front of us, jump somewhere else to
            # keep going. Firstly, pick a gap to jump into.
            gap_starts = [gap_lo
                          for (gap_lo, gap_hi) in program.imem_gaps()
                          if 2 * 4 <= gap_hi - gap_lo]
            assert gap_starts
            gap_lo = random.choice(gap_starts)

            jump_ret = self.jump_gen.gen_tgt(model, program, gap_lo)
            assert jump_ret is not None

            jump_insn, jump_snippet, model = jump_ret
            assert model.pc == gap_lo
            body_snippet = jump_snippet

        real_body_snippet, model = self._gen_loop_stack(model, program)

        if body_snippet is None:
            body_snippet = real_body_snippet
        else:
            body_snippet = Snippet.merge_list([body_snippet,
                                               real_body_snippet])

        return (LoopSnippet(hd_pc, hd_insn, body_snippet, None), model)

    def gen(self,
            cont: GenCont,
            model: Model,
            program: Program) -> Optional[GenRet]:
        space_here = program.get_insn_space_at(model.pc)
        # space_here should always be positive (otherwise we got stuck already)
        assert space_here > 0

        # Give up unless we know our exact loop depth (otherwise, we wouldn't
        # be able to predict the number of loops needed to blow the stack)
        depth = model.loop_stack.min_depth()
        if depth != model.loop_stack.max_depth():
            return None

        num_nests = 1 + LoopStack.stack_depth - depth

        # We know the number of nested loops (num_nests). For each loop, we'll
        # generate zero or more straight-line instructions, a jump if necessary
        # and then the next loop down.
        #
        # Have we got space for what we need to do? Firstly, we need at least 2
        # instructions right here (a loop head plus a jump) unless num_nests is
        # 1, in which case we only need one (the innermost loop head).
        space_needed_here = 1 if num_nests == 1 else 2
        space_here = program.get_insn_space_at(model.pc)
        if space_here < space_needed_here:
            return None

        # Secondly, we can be pessimistic about the number of actual
        # instructions we'll need. If the address space is incredibly
        # fragmented, we'll have to jump on each loop, so we'll end up with a
        # loop head and a jump for each nest except the last, which will just
        # have a loop head. This gives a (slightly) pessimistic number for the
        # space and fuel needed.
        insns_needed = 2 * num_nests - 1
        if program.space < insns_needed or model.fuel < insns_needed:
            return None

        # There's one other possible failure condition. This happens if the
        # free instructions in program.space are made up of a whole load of
        # single instructions. These can't be used for loops. An interval of
        # size N > 1 bytes will support a maximum of N loops (where the
        # innermost loop is the one that causes an error) or N - 1 loops and a
        # jump at the end. We know that we'll be able to make everything work
        # if the sum of "N-1" over the free intervals in the program is at
        # least equal to insns_needed.
        fat_count = 0
        for lo, hi in program.imem_gaps():
            if lo < hi - 1:
                fat_count += hi - lo - 1
        if fat_count < insns_needed:
            return None

        # At this point, we *should* be able to make the loop unconditionally.
        snippet, model = self._gen_loop_stack(model, program)
        return (snippet, model)
