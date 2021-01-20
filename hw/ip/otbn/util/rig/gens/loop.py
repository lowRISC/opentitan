# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import random
from typing import List, Optional, Tuple

from shared.insn_yaml import InsnsFile
from shared.operand import ImmOperandType, RegOperandType, OperandType

from .jump import Jump
from .straight_line_insn import StraightLineInsn
from ..program import ProgInsn, Program
from ..model import Model
from ..snippet import LoopSnippet, Snippet
from ..snippet_gen import GenCont, GenRet, SnippetGen


class Loop(SnippetGen):
    '''A generator that generates a LOOP / LOOPI'''
    def __init__(self, insns_file: InsnsFile) -> None:
        self.jump_gen = Jump(insns_file)
        self.sli_gen = StraightLineInsn(insns_file)

        self.loop = self._get_named_insn(insns_file, 'loop')
        self.loopi = self._get_named_insn(insns_file, 'loopi')

        # loop expects operands: grs, bodysize
        if not (len(self.loop.operands) == 2 and
                isinstance(self.loop.operands[0].op_type, RegOperandType) and
                self.loop.operands[0].op_type.reg_type == 'gpr' and
                isinstance(self.loop.operands[1].op_type, ImmOperandType) and
                not self.loop.operands[1].op_type.signed):
            raise RuntimeError('LOOP instruction from instructions file is not '
                               'the shape expected by the Loop generator.')

        # loopi expects operands: iterations, bodysize
        if not (len(self.loopi.operands) == 2 and
                isinstance(self.loopi.operands[0].op_type, ImmOperandType) and
                not self.loopi.operands[0].op_type.signed and
                isinstance(self.loopi.operands[1].op_type, ImmOperandType) and
                not self.loopi.operands[1].op_type.signed):
            raise RuntimeError('LOOPI instruction from instructions file is not '
                               'the shape expected by the Loop generator.')

    def _pick_iterations(self,
                         op_type: OperandType,
                         bodysize: int,
                         model: Model) -> Optional[Tuple[int, int]]:
        '''Pick the number of iterations for the loop

        If this is a LOOP instruction, op_type will be a RegOperandType. In
        this case, we pick a register whose value we know and which doesn't
        give us a ridiculous number of iterations (checking model.fuel).
        Otherwise, op_type is an ImmOperandType and we pick a reasonable
        iteration count.

        '''
        assert bodysize > 0
        min_fuel_per_iter = 1 if bodysize == 1 else 2
        # model.fuel - 2 is the fuel after executing the LOOP/LOOPI instruction
        # and before executing the minimum-length single-instruction
        # continuation.
        max_iters = (model.fuel - 2) // min_fuel_per_iter

        # Never generate more than 10 iterations (because the instruction
        # sequences would be booooring). Obviously, we'll need to come back to
        # this when filling coverage holes.
        #
        # In general, we'll weight by 1/(1 + abs(iters - 2)). This makes 2 the
        # most likely iteration count (which is good, because 1 iteration is
        # boring).
        max_iters = min(max_iters, 10)

        if isinstance(op_type, RegOperandType):
            assert op_type.reg_type == 'gpr'
            # Iterate over the known registers, trying to pick a weight
            poss_pairs = []  # type: List[Tuple[int, int]]
            weights = []  # type: List[float]
            for idx, value in model.regs_with_known_vals('gpr'):
                if 0 < value <= max_iters:
                    poss_pairs.append((idx, value))
                    # Weight higher iteration counts smaller (1 / count)
                    weights.append(1 / (1 + abs(value - 2)))
            if not poss_pairs:
                return None
            return random.choices(poss_pairs, weights=weights)[0]

        assert isinstance(op_type, ImmOperandType)
        iters_range = op_type.get_op_val_range(model.pc)
        assert iters_range is not None
        iters_lo, iters_hi = iters_range
        if max_iters < max(1, iters_lo):
            return None

        iters_lo = max(iters_lo, 1)
        iters_hi = min(iters_hi, max_iters)

        # Pick a value in [iters_lo, iters_hi], weighting lower values more
        # heavily (1 / count). Since we've made sure that iters_hi <= max_iters
        # <= 10, we don't need to do any clever maths: we can just use
        # random.choices with some weights.
        values = range(iters_lo, 1 + iters_hi)
        weights = []
        for value in values:
            weights.append(1 / (1 + abs(value - 2)))
        num_iters = random.choices(values, weights=weights)[0]
        return (num_iters, num_iters)

    def _pick_loop_shape(self,
                         op0_type: OperandType,
                         op1_type: ImmOperandType,
                         space_here: int,
                         model: Model,
                         program: Program) -> Optional[Tuple[int, int, int]]:
        '''Pick the size of loop and number of iterations

        op_type is the type of the first operand (either 'grs' for loop or
        'iterations' for loopi). space_here is the number of instructions'
        space available at the current position.

        '''
        # The first upper bound on bodysize is that we've got to have an empty
        # space for the loop body.
        #
        # Note: This doesn't allow us to generate a "loop" that encloses
        # previously generated code. So, for example, we couldn't do something
        # like
        #
        #    loopi  10, 3
        #    jal    x0, .+8
        #    jal    x0, .+100  // an isolated instruction that ran earlier
        #    addi   x0, 0      // end of loop
        #
        # Since we can generate jumps in the loop, we might "fill in
        # the middle" afterwards. However, we'll never make a loop that
        # "contains" instructions we executed before.
        #
        # To weaken this, we would need to just require that the end of the
        # loop is not yet taken. But that sounds a bit hard: let's not worry
        # about it for now.
        assert 3 <= space_here
        max_bodysize = space_here - 2

        # Another upper bound comes from program.get_insn_space_left(). If
        # bodysize is 2 or more, our body will need to generate at least 2
        # instructions (either a straight line of length bodysize, or a jump
        # from the start and then a straight line instruction at the end). In
        # this case, we need space for at least 3 instructions (including the
        # LOOP/LOOPI instruction itself).
        #
        # We know that program.get_insn_space_left() is at least 2 (checked in
        # gen()), but if it's 2, we can only have a bodysize of 1.
        assert 2 <= program.space
        if program.space == 2:
            max_bodysize = min(max_bodysize, 1)

        bodysize_range = op1_type.get_op_val_range(model.pc)
        assert bodysize_range is not None
        bs_min, bs_max = bodysize_range
        if max_bodysize < max(1, bs_min):
            return None

        # Decide on the bodysize value. tail_pc is the address of the last
        # instruction in the loop body.
        bodysize = random.randint(max(1, bs_min), min(bs_max, max_bodysize))
        tail_pc = model.pc + 4 * bodysize
        assert program.get_insn_space_at(tail_pc) >= 2

        iters = self._pick_iterations(op0_type, bodysize, model)
        if iters is None:
            return None
        iter_opval, num_iters = iters

        return (iter_opval, num_iters, bodysize)

    def _gen_body(self,
                  bodysize: int,
                  single_iter: bool,
                  bogus_insn: ProgInsn,
                  cont: GenCont,
                  model: Model,
                  program: Program) -> Optional[Tuple[Snippet, Model]]:
        '''Generate the body of a loop

        The model is currently sitting at the start of the loop body.
        model.fuel is assumed to be the amount of fuel needed for a single
        iteration of the loop. If model.fuel is 1, bodysize must also be 1.

        This updates model and program unconditionally, trashing them if it
        returns None.

        '''
        assert 1 <= bodysize
        assert 1 <= model.fuel
        assert bodysize == 1 or model.fuel > 1

        match_addr = model.pc + 4 * bodysize

        # If bodysize is at least 2, we need to generate at least 2
        # instructions (either a straight line of length bodysize, or a jump
        # from the start and then a straight line instruction at the end). We
        # should definitely have space for that.
        min_space_needed = 1 if bodysize == 1 else 2
        assert min_space_needed <= program.space

        # Pick the tail length. The tail is a sequence of straight-line
        # instructions that leads up to the end of the loop body. There must be
        # at least one (part of the spec for a loop).
        #
        # The maximum tail length depends on model.fuel: if bodysize is huge,
        # but fuel is just 2 (say), we can generate a body consisting of a jump
        # to the end and then a single instruction tail.
        #
        # This gives a bound on tail length of model.fuel - 1 (to allow an
        # instruction for the jump), unless bodysize <= model.fuel, in which
        # case we can generate a loop body that's just a tail.
        if bodysize <= model.fuel:
            max_tail_len = bodysize
        else:
            max_tail_len = min(bodysize, model.fuel - 1)

        # program.space gives another bound on the tail length. If the bodysize
        # is large enough that we'll need to jump to the tail, the tail can't
        # be more than program.space - 1 in length. If we don't need to
        # generate a jump instruction, it can be up to program.space.
        if bodysize <= program.space:
            max_tail_len = min(max_tail_len, program.space)
        else:
            assert 2 <= program.space
            max_tail_len = min(max_tail_len, program.space - 1)

        assert max_tail_len >= 1
        tail_len = random.randint(1, max_tail_len)

        # When we're generating the body of the loop, we mustn't update a
        # register whose value we relied on. For example, we might know that x3
        # contains 0x20 and use it as a load address, but then write 0x30 to
        # it. This will go badly when we come around again!
        #
        # To avoid the problem, we explicitly pick the registers that we are
        # going to leave unmolested and mark them as special in the model. We
        # then write None to all other known registers (to model the fact that
        # they have *some* architectural value; we just don't know what it is).
        #
        # Mark 50% of these registers as not-to-be-touched.
        #
        # This pass is skipped if we know we're doing exactly one iteration
        const_token = model.push_const()
        if not single_iter:
            for rt, regs in model.all_regs_with_known_vals().items():
                for reg_idx, _ in regs:
                    if random.random() < 0.5:
                        model.mark_const(rt, reg_idx)
                    else:
                        model.forget_value(rt, reg_idx)

            # Unconditionally mark x1 as constant, to avoid unbalanced push/pop
            # sequences in the loop.
            #
            # TODO: This means we don't use x1 inside loop bodies; we need to
            # fix that.
            model.mark_const('gpr', 1)

        # If the tail isn't the entire loop, generate the first part of the
        # loop body. While doing so, we constrain fuel (to save enough for the
        # tail) and work with a program where we've inserted copies of a dummy
        # instruction over all the addresses that tail will use, plus the first
        # instruction after the loop.
        head_snippet = None
        assert tail_len <= bodysize
        tail_start = model.pc + 4 * (bodysize - tail_len)
        if tail_len < bodysize:
            assert tail_len < model.fuel
            model.fuel -= tail_len + 1

            if model.fuel > 0:
                # If there's some fuel for a head that isn't just a jump to the
                # tail, generate it here.
                prog0 = program.copy()
                bogus_tail_insns = [bogus_insn] * (tail_len + 1)
                prog0.add_insns(tail_start, bogus_tail_insns)

                head_snippet, model = cont(model, prog0)

                # Generation of the head might have failed, but that's actually
                # ok: we'll just start the loop body with the jump to the tail.
                # If it succeeded, add its instructions to program.
                if head_snippet is not None:
                    head_snippet.insert_into_program(program)

            # Add one back to model.fuel for the jump instruction we might need
            # to get to the tail.
            model.fuel += 1

            if model.pc != tail_start:
                # If model hasn't ended up at tail_start, insert a jump to get
                # there. Use program rather than prog0 because prog0 has a
                # dummy instruction in the way. Note that jump_gen.gen_tgt will
                # insert the jump instruction that it generates into program.
                jump_ret = self.jump_gen.gen_tgt(model, program, tail_start)
                if jump_ret is None:
                    return None

                jump_snippet, model = jump_ret
                assert model.pc == tail_start

                head_snippet = Snippet.cons_option(head_snippet, jump_snippet)

            # Add tail_len fuel back to model (undoing the rest of the
            # subtraction we did before we started generating the head)
            model.fuel += tail_len

            # We should always have generated at least something at this point
            # (because the original value of model.pc can't have been
            # tail_start if tail_len was less than bodysize).
            #
            # We've also updated the model as if it just ran the head and have
            # inserted head_snippet into program.
            assert head_snippet is not None

        # At this point, we've generated any head snippet and model.pc now
        # points at tail_start. Generate the remaining straight line
        # instructions that we need.
        assert model.pc == tail_start
        tail_ret = self.sli_gen.gen_some(tail_len, model, program)
        if tail_ret is None:
            return None

        tail_snippet, model = tail_ret
        assert model.pc == match_addr

        snippet = Snippet.cons_option(head_snippet, tail_snippet)

        # Remove the const annotations that we added to the model
        model.pop_const(const_token)
        return (snippet, model)

    def gen(self,
            cont: GenCont,
            model: Model,
            program: Program) -> Optional[GenRet]:

        # A loop or loopi sequence has a loop/loopi instruction, at least one
        # body instruction (the last of which must be a straight line
        # instruction) and then needs a following trampoline. That means we
        # need at least 3 instructions' space at the current PC.
        space_here = program.get_insn_space_at(model.pc)
        if space_here < 3:
            return None

        # The smallest possible loop takes 2 instructions (the loop instruction
        # plus the single-instruction loop body)
        if program.space < 2:
            return None

        # Don't blow the loop stack
        if model.loop_depth == Model.max_loop_depth:
            return None

        # Decide whether to generate LOOP or LOOPI
        loop_weight = 1.0
        loopi_weight = 1.0
        sum_weights = loop_weight + loopi_weight
        is_loop = random.random() < loop_weight / sum_weights
        insn = self.loop if is_loop else self.loopi

        # Pick a loop count
        op0_type = insn.operands[0].op_type
        op1_type = insn.operands[1].op_type
        assert isinstance(op1_type, ImmOperandType)
        lshape = self._pick_loop_shape(op0_type,
                                       op1_type, space_here, model, program)
        if lshape is None:
            return None

        iter_opval, num_iters, bodysize = lshape

        # Generate the head instruction (which runs once, unconditionally) and
        # clone model and program to add it
        hd_addr = model.pc
        enc_bodysize = op1_type.op_val_to_enc_val(bodysize, model.pc)
        assert enc_bodysize is not None
        hd_insn = ProgInsn(insn, [iter_opval, enc_bodysize], None)

        body_program = program.copy()
        body_program.add_insns(model.pc, [hd_insn])

        body_model = model.copy()
        body_model.update_for_insn(hd_insn)
        body_model.pc += 4
        body_model.loop_depth += 1
        assert body_model.loop_depth <= Model.max_loop_depth

        # Constrain fuel in body_model: subtract one (for the first instruction
        # after the loop) and then divide by the number of iterations. When we
        # picked num_iters, we made sure this was still positive.
        #
        # The minimum fuel to give is 1 if bodysize is 1 or 2 otherwise
        # (because the shortest possible sequence is a jump to the last
        # instruction, then a straight line instruction).
        min_fuel_per_iter = 1 if bodysize == 1 else 2
        max_fuel_per_iter = (body_model.fuel - 1) // num_iters
        assert min_fuel_per_iter <= max_fuel_per_iter
        fuel_per_iter = random.randint(min_fuel_per_iter, max_fuel_per_iter)
        body_model.fuel = fuel_per_iter

        body_ret = self._gen_body(bodysize,
                                  num_iters == 1,
                                  hd_insn,
                                  cont, body_model, body_program)
        if body_ret is None:
            return None

        body_snippet, body_model = body_ret
        assert body_model.loop_depth == model.loop_depth + 1
        body_model.loop_depth -= 1

        # Calculate the actual amount of fuel that we used
        body_fuel = fuel_per_iter - body_model.fuel
        assert body_fuel > 0
        fuel_afterwards = model.fuel - num_iters * body_fuel

        snippet = LoopSnippet(hd_addr, hd_insn, body_snippet)
        snippet.insert_into_program(program)

        # Update model to take the loop body into account. If we know we have
        # exactly one iteration through the body, we can just take body_model.
        # Otherwise, we merge the two after "teleporting" model to the loop
        # match address.
        assert body_model.pc == model.pc + 4 * (1 + bodysize)
        if num_iters == 1:
            model = body_model
        else:
            model.update_for_insn(hd_insn)
            model.pc = body_model.pc
            model.merge(body_model)

            # Fix up model.fuel: the merge function will have taken the minimum
            # between model and body_model, but we actually want it to be what
            # we computed before.
            model.fuel = fuel_afterwards

        return (snippet, model)
