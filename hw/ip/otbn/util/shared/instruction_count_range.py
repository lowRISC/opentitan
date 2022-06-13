#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from enum import Enum
from math import inf
from typing import Optional, Tuple

from .control_flow import (ControlGraph, Cycle, Ecall, ImemEnd, LoopEnd,
                           LoopStart, Ret, program_control_graph,
                           subroutine_control_graph)
from .decode import OTBNProgram


class StopPoint(Enum):
    LOOP_END = 'loop end'
    RET = 'ret'
    ECALL = 'ecall'


def _get_insn_count_range(program: OTBNProgram, graph: ControlGraph,
                          start_pc: int,
                          stop_at: StopPoint) -> Tuple[int, int]:
    '''Return minimum and maximum instruction counts across control paths.

    In the presence of control-flow cycles or loops with a non-constant
    number of iterations, the maximum number of iterations will be
    None, because there's no clear maximum number of times the loop/cycle
    could run.

    The `stop_at` parameter indicates the expected end point of the control
    flow path(s) from this starting point. It is not currently supported for
    control flow paths from a single start point to have different endings --
    for instance, for one branch to end the program with `ecall` and another to
    return to the caller with `ret`. This is because, for instance, if this
    function is called recursively on a subroutine (stop_at = RET), then the
    caller needs to know the min/max instruction count *after the subroutine
    call returns*, and it would require substantial additional tracking to
    account for some additional, separate path that ends the program entirely.

    In all cases, the function will raise an error if it encounters one of the
    other stopping points; for instance, if an `ecall` instruction appears when
    `stop_at` = RET, then there will be an error. The function will return the
    min/max instruction counts across *all control-flow paths* from the given
    start point to the stopping point.
    '''
    section, edges = graph.get_entry(start_pc)
    sec_count = len(section.get_insn_sequence(program))

    # Special case for when we're in a loop; if we have the loop end and one
    # other edge, this represents the option to either continue the loop or
    # stop. In this case, we don't want to follow the "stop" branch, but rather
    # simply return the min/max from ending the loop here.
    if any([isinstance(e, LoopEnd) for e in edges]):
        assert stop_at == StopPoint.LOOP_END
        # At a loop end, we expect exactly two edges; one to end the loop and
        # one to go back to the start and do another iteration.
        assert len(edges) == 2
        return (sec_count, sec_count)

    # Find the minimum/maximum instruction counts for all next edges.
    min_count = inf
    max_count = sec_count
    for loc in edges:
        if isinstance(loc, Ecall) or isinstance(loc, ImemEnd):
            assert stop_at == StopPoint.ECALL
            loc_min, loc_max = 0, 0
        elif isinstance(loc, Ret):
            assert stop_at == StopPoint.RET
            loc_min, loc_max = 0, 0
        elif isinstance(loc, LoopEnd):
            # All LoopEnds should have been handled above!
            assert False, f'Unexpected loop end at PC {section.end:#x}'
        elif isinstance(loc, LoopStart):
            # Calculate the number of iterations if possible.
            insn = program.get_insn(section.end)
            if insn.mnemonic == 'loopi':
                op_vals = program.get_operands(section.end)
                num_iterations = op_vals['iterations']
                loop_min, loop_max = _get_insn_count_range(
                    program, graph, loc.loop_start_pc, StopPoint.LOOP_END)
                loop_min *= num_iterations
                loop_max *= num_iterations
            else:
                # Cannot determine # iterations statically.
                loop_min, loop_max = 0, inf

            # Calculate the instruction count range after the loop.
            post_loop_min, post_loop_max = _get_insn_count_range(
                program, graph, loc.loop_end_pc + 4, stop_at)
            loc_min = loop_min + post_loop_min
            loc_max = loop_max + post_loop_max
        elif isinstance(loc, Cycle):
            # For cycles, the minimum is 0 (if the cycle is never traversed)
            # and the maximum is None (because we can't easily calculate
            # statically how many times the cycle will be traversed).
            loc_min, loc_max = 0, inf
        else:
            insn = program.get_insn(section.end)
            operands = program.get_operands(section.end)
            if insn.mnemonic == 'jal' and operands['grd'] == 1:
                # Jumping to another subroutine; count the range for the
                # subroutine itself.
                jump_min, jump_max = _get_insn_count_range(
                    program, graph, loc.pc, StopPoint.RET)
                # Calculate the instruction count range after returning from
                # the jump.
                post_jump_min, post_jump_max = _get_insn_count_range(
                    program, graph, section.end + 4, stop_at)
                loc_min = jump_min + post_jump_min
                loc_max = jump_max + post_jump_max
            else:
                # If not a jump, then this is just a normal PC (i.e. a branch).
                # Follow the branch to get the min/max range.
                loc_min, loc_max = _get_insn_count_range(
                    program, graph, loc.pc, stop_at)

        # Merge the min/max for this location into the final result
        min_count = min(min_count, sec_count + loc_min)
        max_count = max(max_count, sec_count + loc_max)

    return (min_count, max_count)


def program_insn_count_range(
        program: OTBNProgram) -> Tuple[int, Optional[int]]:
    '''Return minimum and maximum instruction counts for the program.

    Wrapper for `_get_insn_count_range` that works on the full program; it
    starts at graph.start and returns the instruction counts for all paths that
    lead to the end of the program.
    '''
    graph = program_control_graph(program)
    min_count, max_count = _get_insn_count_range(program, graph, graph.start,
                                                 StopPoint.ECALL)
    if max_count == inf:
        max_count = None
    return min_count, max_count


def subroutine_insn_count_range(program: OTBNProgram,
                                subroutine: str) -> Tuple[int, Optional[int]]:
    '''Return minimum and maximum instruction counts for the subroutine.

    Wrapper for `_get_insn_count_range` that works on a subroutine; it starts
    at graph.start and returns the instruction counts for all paths that lead
    to a return to the original caller. If a path leads to the program ending
    (i.e. an `ecall` instruction), then there will be an error.
    '''
    graph = subroutine_control_graph(program, subroutine)
    min_count, max_count = _get_insn_count_range(program, graph, graph.start,
                                                 StopPoint.RET)
    if max_count == inf:
        max_count = None
    return min_count, max_count
