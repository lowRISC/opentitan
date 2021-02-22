# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from typing import List, Optional

from .err_bits import LOOP
from .trace import Trace


class TraceLoopStart(Trace):
    def __init__(self, iterations: int, bodysize: int):
        self.iterations = iterations
        self.bodysize = bodysize

    def trace(self) -> str:
        return "Start LOOP, {} iterations, bodysize: {}".format(
            self.iterations, self.bodysize)


class TraceLoopIteration(Trace):
    def __init__(self, iteration: int, total: int):
        self.iteration = iteration
        self.total = total

    def trace(self) -> str:
        return "LOOP iteration {}/{}".format(self.iteration, self.total)


class LoopLevel:
    '''An object representing a level in the current loop stack

    start_addr is the first instruction inside the loop (the instruction
    following the loop instruction). insn_count is the number of instructions
    in the loop (and must be positive). restarts is one less than the number of
    iterations, and must be non-negative.

    '''
    def __init__(self, start_addr: int, insn_count: int, restarts: int):
        assert 0 <= start_addr
        assert 0 < insn_count
        assert 0 <= restarts

        self.loop_count = 1 + restarts
        self.restarts_left = restarts
        self.start_addr = start_addr
        self.match_addr = start_addr + 4 * insn_count


class LoopStack:
    '''An object representing the loop stack

    The loop stack holds up to 8 LoopLevel objects, corresponding to nested
    loops.

    '''
    stack_depth = 8

    def __init__(self) -> None:
        self.stack = []  # type: List[LoopLevel]
        self.trace = []  # type: List[Trace]
        self.err_flag = False

    def start_loop(self,
                   next_addr: int,
                   loop_count: int,
                   insn_count: int) -> None:
        '''Start a loop.

        next_addr is the address of the first instruction in the loop body.
        loop_count must be positive and is the number of times to execute the
        loop. insn_count must be positive and is the number of instructions in
        the loop body.

        '''
        assert 0 <= next_addr
        assert 0 < insn_count
        assert 0 < loop_count

        if len(self.stack) == LoopStack.stack_depth:
            self.err_flag = True

        self.trace.append(TraceLoopStart(loop_count, insn_count))
        self.stack.append(LoopLevel(next_addr, insn_count, loop_count - 1))

    def check_insn(self, pc: int, insn_affects_control: bool) -> None:
        '''Check for branch instructions at the end of a loop body'''
        if self.stack:
            top = self.stack[-1]
            if pc + 4 == top.match_addr:
                # We're about to execute the last instruction in the loop body.
                # Make sure that it isn't a jump, branch or another loop
                # instruction.
                if insn_affects_control:
                    self.err_flag = True

    def step(self, next_pc: int) -> Optional[int]:
        '''Update loop stack. If we should loop, return new PC'''
        if self.stack:
            top = self.stack[-1]

            if next_pc == top.match_addr:
                assert top.restarts_left >= 0

                # 1-based iteration number
                loop_idx = top.loop_count - top.restarts_left

                if not top.restarts_left:
                    self.stack.pop()
                    ret_val = None
                else:
                    top.restarts_left -= 1
                    ret_val = top.start_addr

                self.trace.append(TraceLoopIteration(loop_idx, top.loop_count))
                return ret_val

        return None

    def err_bits(self) -> int:
        return LOOP if self.err_flag else 0

    def changes(self) -> List[Trace]:
        return self.trace

    def commit(self) -> None:
        assert not self.err_flag
        self.trace = []

    def abort(self) -> None:
        self.trace = []
        self.err_flag = False
