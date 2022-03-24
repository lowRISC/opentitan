# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import random
from typing import List, Optional, Tuple

from shared.insn_yaml import Insn, InsnsFile
from shared.operand import ImmOperandType, RegOperandType, OperandType

from .jump import Jump
from .straight_line_insn import StraightLineInsn
from ..config import Config
from ..program import ProgInsn, Program
from ..model import LoopStack, Model
from ..snippet import LoopSnippet, ProgSnippet, Snippet
from ..snippet_gen import GenCont, GenRet, SnippetGen


class Loop(SnippetGen):
    '''A generator that generates a LOOP / LOOPI'''
    # An iteration count: the encoded value, the implied number of iterations
    # and a possible loop warp.
    IterCount = Tuple[int, int, Optional[LoopSnippet.Warp]]

    # The shape of a loop that's being generated. Consists of bodysize and an
    # iteration count, as described above.
    Shape = Tuple[int, IterCount]

    # The individual pieces of a generated loop. The tuple is (bodysize,
    # hd_insn, body_snippet, model_afterwards, warp)
    Pieces = Tuple[int, ProgInsn, Snippet, Model, Optional[LoopSnippet.Warp]]

    def __init__(self, cfg: Config, insns_file: InsnsFile) -> None:
        super().__init__()

        self.jump_gen = Jump(cfg, insns_file)
        self.sli_gen = StraightLineInsn(cfg, insns_file)

        self.loop = self._get_named_insn(insns_file, 'loop')
        self.loopi = self._get_named_insn(insns_file, 'loopi')

        self.loopi_prob = 0.5

        loop_weight = cfg.insn_weights.get('loop')
        loopi_weight = cfg.insn_weights.get('loopi')
        sum_weights = loop_weight + loopi_weight
        if sum_weights == 0:
            self.disabled = True
        else:
            self.loopi_prob = loopi_weight / sum_weights

        self.cfg_max_iters = cfg.ranges.get_max('loop-iters')
        if self.cfg_max_iters is not None and self.cfg_max_iters < 1:
            raise RuntimeError(f'Invalid max-loop-iters value of '
                               f'{self.cfg_max_iters}: this must be '
                               f'at least 1.')

        self.cfg_max_tail = cfg.ranges.get_max('loop-tail-insns')
        if self.cfg_max_tail is not None and self.cfg_max_tail < 1:
            raise RuntimeError(f'Invalid max-loop-tail-insns value of '
                               f'{self.cfg_max_tail}: this must be '
                               f'at least 1.')

    def _pick_loop_iterations(self,
                              max_iters: int,
                              model: Model) -> Optional[IterCount]:
        '''Pick the number of iterations for a LOOP loop

        To do this, we pick a register whose value we know and which doesn't
        give us a ridiculous number of iterations (checking model.fuel).
        max_iters is the maximum number of iterations possible, given how much
        fuel we have left.

        Returns a tuple (idx, iters, warp) where idx is the register index,
        iters is the number of iterations that will run and warp is either None
        or is a pair (from, to) giving a loop warp that should apply. iters
        will always be at most max_iters.

        '''
        # Most of the time, we want to generate a very small number of
        # iterations (since each iteration runs the same instructions, there's
        # not much point in generating lots of them). However, we don't want to
        # pick 1 iteration too often (since that's equivalent to no loop at
        # all). To implement this, we use a weighting of 1/(1 + abs(x - 2)) and
        # restrict to nonzero values less than 10.
        #
        # However we also have a coverage point that we'd like to hit where we
        # generate the maximal number of iterations. Thus we also allow the
        # case where a register is all ones and give it a weighting of 0.001:
        # we shouldn't hit this very often (and only need to see it once). In
        # practice, this will mostly come up because we decided to do a LOOP
        # and the only nonzero known value is 0xffffffff. We only allow this if
        # max_iters is at least 10.
        max_iters = min(max_iters, 10)
        if self.cfg_max_iters is not None:
            max_iters = min(max_iters, self.cfg_max_iters)

        allow_maximal_loop = max_iters >= 10

        # Iterate over the known registers, trying to pick a weight
        poss_pairs = []  # type: List[Tuple[int, int]]
        weights = []  # type: List[float]
        for idx, value in model.regs_with_known_vals('gpr'):
            weight = 0.0
            if 0 < value <= max_iters:
                weight = 1 / (1 + abs(value - 2))
            elif allow_maximal_loop and value == (1 << 32) - 1:
                weight = 0.001
            if weight:
                poss_pairs.append((idx, value))
                weights.append(weight)

        if not poss_pairs:
            return None

        idx, actual_iters = random.choices(poss_pairs, weights=weights)[0]
        if actual_iters <= max_iters:
            warp = None
            iters = actual_iters
        else:
            # We will start '1 + lo' iterations before the warp (and finish
            # 'lo' of them). We'll then finish 'max_iters - lo' iterations
            # after the warp. Both '1 + lo' and 'max_iters - lo' must be
            # positive.
            lo = random.randint(0, max_iters - 1)
            hi = actual_iters - (max_iters - lo)
            assert 0 <= lo <= hi < actual_iters
            warp = (lo, hi)
            iters = max_iters

        return (idx, iters, warp)

    def _pick_loopi_iterations(self,
                               max_iters: int,
                               op_type: OperandType,
                               model: Model) -> Optional[IterCount]:
        '''Pick the number of iterations for a LOOPI loop

        max_iters is the maximum number of iterations possible, given how much
        fuel we have left.

        Returns the encoded and decoded number of iterations.

        '''

        assert isinstance(op_type, ImmOperandType)
        iters_range = op_type.get_op_val_range(model.pc)
        assert iters_range is not None
        iters_lo, iters_hi = iters_range

        # Constrain iters_hi if the max-loop-iters configuration value was set.
        if self.cfg_max_iters is not None:
            iters_hi = min(iters_hi, self.cfg_max_iters)
            if iters_hi < iters_lo:
                return None

        # Very occasionally, generate iters_hi iterations (the maximum number
        # representable) if we've got fuel for it. We don't do this often,
        # because the instruction sequence will end up just testing loop
        # handling and be very inefficient for testing anything else.
        if max_iters >= iters_hi and random.random() < 0.01:
            enc_val = op_type.op_val_to_enc_val(iters_hi, model.pc)
            # This should never fail, because iters_hi was encodable.
            assert enc_val is not None
            return (enc_val, iters_hi, None)

        # The rest of the time, we don't usually (95%) generate more than 3
        # iterations (because the instruction sequences are rather
        # repetitive!). Also, don't generate 0 iterations here, even though
        # it's encodable. That causes an error, so we'll do that in a separate
        # generator.
        if random.random() < 0.95:
            tgt_max_iters = min(max_iters, 3)
        else:
            tgt_max_iters = 10000

        ub = min(iters_hi, max_iters, tgt_max_iters)
        lb = max(iters_lo, 1)

        if ub < lb:
            return None

        # Otherwise, pick a value uniformly in [iters_lo, iters_hi]. No need
        # for clever weighting: in the usual case, there are just 3
        # possibilities!
        num_iters = random.randint(lb, ub)
        enc_val = op_type.op_val_to_enc_val(num_iters, model.pc)
        # This should never fail: the choice should have been in the encodable
        # range.
        assert enc_val is not None
        return (enc_val, num_iters, None)

    def pick_iterations(self,
                        op_type: OperandType,
                        bodysize: int,
                        model: Model) -> Optional[IterCount]:
        '''Pick the number of iterations for a loop

        Returns the encoded value (register index or encoded number of
        iterations), together with the number of iterations that implies.

        '''
        assert bodysize > 0
        min_fuel_per_iter = 1 if bodysize == 1 else 2

        # model.fuel - 2 is the fuel after executing the LOOP/LOOPI instruction
        # and before executing the minimum-length single-instruction
        # continuation.
        max_iters = (model.fuel - 2) // min_fuel_per_iter

        if isinstance(op_type, RegOperandType):
            assert op_type.reg_type == 'gpr'
            return self._pick_loop_iterations(max_iters, model)
        else:
            assert isinstance(op_type, ImmOperandType)
            return self._pick_loopi_iterations(max_iters, op_type, model)

    def _pick_loop_shape(self,
                         op0_type: OperandType,
                         op1_type: ImmOperandType,
                         space_here: int,
                         check: bool,
                         model: Model,
                         program: Program) -> Optional[Shape]:
        '''Pick the size of loop and number of iterations

        op0_type is the type of the first operand (either 'grs' for loop or
        'iterations' for loopi). op1_type is the type of the bodysize operand.

        space_here is the number of instructions' space available at the
        current position. If check is true, we're generating a genuine loop and
        should perform checks like making sure there's enough space to generate
        everything.

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

        # Another upper bound comes from program.space. If bodysize is 2 or
        # more, our body will need to generate at least 2 instructions (either
        # a straight line of length bodysize, or a jump from the start and then
        # a straight line instruction at the end). In this case, we need space
        # for at least 3 instructions (including the LOOP/LOOPI instruction
        # itself).
        #
        # We know that program.space is at least 2 (checked in gen()), but if
        # it's 2, we can only have a bodysize of 1.
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
        if check:
            tail_pc = model.pc + 4 * bodysize
            assert program.get_insn_space_at(tail_pc) >= 2

        iters = self.pick_iterations(op0_type, bodysize, model)
        if iters is None:
            return None

        return (bodysize, iters)

    def _gen_tail_insns(self,
                        num_insns: int,
                        model: Model,
                        program: Program) -> Optional[Tuple[List[ProgInsn],
                                                            Model]]:
        return self.sli_gen.gen_some(num_insns, model, program)

    def _gen_tail(self,
                  num_insns: int,
                  model: Model,
                  program: Program) -> Optional[Tuple[Snippet, Model]]:
        pc = model.pc
        ret = self._gen_tail_insns(num_insns, model, program)
        if ret is None:
            return None

        insns, model = ret
        assert len(insns) == num_insns

        snippet = ProgSnippet(pc, insns)
        snippet.insert_into_program(program)

        return (snippet, model)

    def _gen_body(self,
                  bodysize: int,
                  single_iter: bool,
                  bogus_insn: ProgInsn,
                  cont: GenCont,
                  model: Model,
                  program: Program) -> Optional[GenRet]:
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

        if self.cfg_max_tail is not None:
            max_tail_len = min(max_tail_len, self.cfg_max_tail)

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

                head_snippet, model = cont(model, prog0, False)

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

                jump_insn, jump_snippet, model = jump_ret
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
        tail_ret = self._gen_tail(tail_len, model, program)
        if tail_ret is None:
            return None

        tail_snippet, model = tail_ret
        assert model.pc == match_addr

        snippet = Snippet.cons_option(head_snippet, tail_snippet)

        # Remove the const annotations that we added to the model
        model.pop_const(const_token)
        return (snippet, model)

    def pick_loop_insn(self) -> Insn:
        '''Pick either LOOP or LOOPI'''
        is_loopi = random.random() < self.loopi_prob
        return self.loopi if is_loopi else self.loop

    def _setup_body(self,
                    hd_insn: ProgInsn,
                    end_addr: int,
                    model: Model,
                    program: Program,
                    has_warp: bool) -> Tuple[Model, Optional[LoopStack]]:
        '''Set up a Model for use in body; insert hd_insn into program

        This may hack model.loop_stack to avoid generating further loops. If it
        does so, it will return the "real" loop stack as a second return value.

        '''
        body_model = model.copy()
        body_model.update_for_insn(hd_insn)
        body_model.pc += 4
        body_model.loop_stack.push(end_addr)

        program.add_insns(model.pc, [hd_insn])

        # If the loop we're generating has an associated warp, we want to avoid
        # generating any more loops in the body. It's really bad if we generate
        # a loop or loopi instruction as the first instruction of the body
        # (because it breaks the warping). But there's also no real benefit to
        # allowing it, so let's not. To avoid generating any more loops, we
        # hack the loop stack to pretend it is full.
        ret_loop_stack = None
        if has_warp:
            ret_loop_stack = body_model.loop_stack.copy()
            body_model.loop_stack.force_full()

        return (body_model, ret_loop_stack)

    def _pick_head(self,
                   space_here: int,
                   check: bool,
                   model: Model,
                   program: Program) -> Optional[Tuple[ProgInsn, Shape]]:
        insn = self.pick_loop_insn()

        # Pick a loop count
        op0_type = insn.operands[0].op_type
        op1_type = insn.operands[1].op_type
        assert isinstance(op1_type, ImmOperandType)
        lshape = self._pick_loop_shape(op0_type, op1_type,
                                       space_here, check, model, program)
        if lshape is None:
            return None

        bodysize, iters = lshape

        # Extract the encoded operand value from iters. We ignore num_iters and
        # warp: they will be used in gen_pieces (returned in lshape), but we
        # don't need them here.
        iter_opval, num_iters, warp = iters

        # Generate the head instruction (which runs once, unconditionally) and
        # clone model and program to add it
        enc_bodysize = op1_type.op_val_to_enc_val(bodysize, model.pc)
        assert enc_bodysize is not None
        return (ProgInsn(insn, [iter_opval, enc_bodysize], None), lshape)

    def _gen_pieces(self,
                    cont: GenCont,
                    model: Model,
                    program: Program) -> Optional[Pieces]:
        '''Generate a loop and return its constituent pieces

        This is useful for subclasses that alter the generated loop after the
        fact.

        If this function succeeds, it may modify model (but it will not insert
        the generated instructions into program).

        '''
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
        if model.loop_stack.maybe_full():
            return None

        ret = self._pick_head(space_here, True, model, program)
        if ret is None:
            return None

        hd_insn, lshape = ret
        bodysize, iters = lshape
        iter_opval, num_iters, warp = iters

        # The address of the final instruction in the loop
        end_addr = model.pc + 4 * bodysize

        body_program = program.copy()
        body_model, body_loop_stack = self._setup_body(hd_insn, end_addr,
                                                       model, body_program,
                                                       warp is not None)

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

        # If we hacked the loop stack in _setup_body, the "correct" value of
        # the loop stack is in body_loop_stack. Put it back.
        if body_loop_stack is not None:
            body_model.loop_stack = body_loop_stack

        body_model.loop_stack.pop(end_addr)

        # Calculate the actual amount of fuel that we used
        body_fuel = fuel_per_iter - body_model.fuel
        assert body_fuel > 0
        fuel_afterwards = model.fuel - num_iters * body_fuel

        # Update model to take the loop body into account. For the loop stack
        # state, we just take whatever's in body_model. If everything was well
        # balanced, this will match anyway (and, if not, it's the state that
        # OTBN will be in at the end of the loop).
        #
        # For registers, if we know we have exactly one iteration through the
        # body, we can just take them from body_model. Otherwise, we merge the
        # two after "teleporting" model to the loop match address.
        assert body_model.pc == end_addr + 4
        if num_iters == 1:
            model = body_model
        else:
            model.update_for_insn(hd_insn)
            model.loop_stack = body_model.loop_stack
            model.pc = body_model.pc
            model.merge(body_model)

            # Fix up model.fuel: the merge function will have taken the minimum
            # between model and body_model, but we actually want it to be what
            # we computed before.
            model.fuel = fuel_afterwards

        return (bodysize, hd_insn, body_snippet, model, warp)

    def gen(self,
            cont: GenCont,
            model: Model,
            program: Program) -> Optional[GenRet]:

        hd_addr = model.pc
        pieces = self._gen_pieces(cont, model, program)
        if pieces is None:
            return None

        shape, hd_insn, body_snippet, model, warp = pieces

        snippet = LoopSnippet(hd_addr, hd_insn, body_snippet, warp)
        snippet.insert_into_program(program)

        return (snippet, model)
