#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import argparse
import sys
from typing import List

from shared.check import CheckResult
from shared.decode import OTBNProgram, decode_elf
from shared.section import CodeSection


def _get_pcs_for_mnemonics(program: OTBNProgram,
                           mnems: List[str]) -> List[int]:
    '''Gets all PCs in the program holding the given instruction.'''
    return [
        pc for (pc, (insn, _)) in program.insns.items()
        if insn.mnemonic in mnems
    ]


def _get_branches(program: OTBNProgram) -> List[int]:
    '''Gets the PCs of all branch instructions (BEQ and BNE) in the program.'''
    return _get_pcs_for_mnemonics(program, ['bne', 'beq'])


def _get_loop_starts(program: OTBNProgram) -> List[int]:
    '''Gets the start PCs of all loops (LOOP and LOOPI) in the program.'''
    return _get_pcs_for_mnemonics(program, ['loop', 'loopi'])


def _get_loops(program: OTBNProgram) -> List[CodeSection]:
    '''Gets the PC ranges of all loops (LOOP and LOOPI) in the program.'''
    loop_starts = _get_loop_starts(program)
    loops = []
    for pc in loop_starts:
        operands = program.get_operands(pc)
        end_pc = pc + operands['bodysize'] * 4
        loops.append(CodeSection(pc + 4, end_pc))
    return loops


def _check_loop_iterations(program: OTBNProgram,
                           loops: List[CodeSection]) -> CheckResult:
    '''Checks number of iterations for loopi.

    If the number of iterations is 0, this check fails; `loopi` requires at
    least one iteration and will raise a LOOP error otherwise. The `loop`
    instruction also has this requirement, but since the number of loop
    iterations comes from a register it's harder to check statically and is not
    considered here.
    '''
    out = CheckResult()
    for loop in loops:
        insn = program.get_insn(loop.start)
        operands = program.get_operands(loop.start)
        if insn.mnemonic == 'loopi' and operands['iterations'] <= 0:
            out.err(
                'Bad number of loop iterations ({}) at PC {:#x}: {}'.format(
                    operands['iterations'], loop.start,
                    insn.disassemble(loop.start, operands)))
    return out


def _check_loop_end_insns(program: OTBNProgram,
                          loops: List[CodeSection]) -> CheckResult:
    '''Checks that loops do not end in control flow instructions.

    Such instructions can cause LOOP software errors during execution.
    '''
    out = CheckResult()
    for loop in loops:
        loop_end_insn = program.get_insn(loop.end)
        if not loop_end_insn.straight_line:
            out.err('Control flow instruction ({}) at end of loop at PC {:#x} '
                    '(loop starting at PC {:#x})'.format(
                        loop_end_insn.mnemonic, loop.end, loop.start))
    return out


def _check_loop_inclusion(program: OTBNProgram,
                          loops: List[CodeSection]) -> CheckResult:
    '''Checks that inner loops are fully contained within outer loops.

    When a loop starts within the body of another loop, it must be the case
    that the inner loop's final instruction occurs before the outer loop's.
    '''
    out = CheckResult()
    for loop in loops:
        for other in loops:
            if other.start in loop and other.end not in loop:
                out.err('Inner loop ends after outer loop (inner loop {}, '
                        'outer loop {})'.format(other, loop.pretty()))

    return out


def _check_loop_branching(program: OTBNProgram,
                          loops: List[CodeSection]) -> CheckResult:
    '''Checks that there are no branches into or out of loop bodies.

    Branches within the same loop body are permitted (but not branches from an
    inner loop to an outer loop, as this counts as branching out of the inner
    loop). Because this isn't necessarily a fatal issue (for instance, it's
    possible the branched-to code will always return to the loop), this check
    returns warnings rather than errors.

    A `jal` instruction with a register other than `x1` as the first operand is
    treated the same as a branch and not permitted to cross the loop-body
    boundary.
    '''
    out = CheckResult()

    # Check all bne and beq instructions, as well as `jal` instructions with
    # first operands other than x1 (unconditional branch)
    to_check = _get_branches(program)
    for pc in _get_pcs_for_mnemonics(program, ['jal']):
        operands = program.get_operands(pc)
        if operands['grd'] != 1:
            to_check.append(pc)

    for pc in to_check:
        operands = program.get_operands(pc)
        branch_addr = operands['offset'] & ((1 << 32) - 1)

        # Get the loop bodies the branch is inside, if any
        current_loops = []
        for loop in loops:
            if pc in loop:
                current_loops.append(loop)

        # Check that we're not branching out of any loop bodies
        for loop in current_loops:
            if branch_addr not in loop:
                insn = program.get_insn(pc)
                out.warn(
                    'Branch out of loop at PC {:#x} (loop from PC {:#x} to PC '
                    '{:#x}, branch {} to PC {:#x}). This might cause problems '
                    'with the loop stack and surprising behavior.'.format(
                        pc, loop.start, loop.end, insn.mnemonic, branch_addr))

        # Check that we're not branching *into* a loop body that the branch
        # instruction is not already in
        for loop in loops:
            if (branch_addr in loop) and (loop not in current_loops):
                out.warn(
                    'Branch into loop at PC {:#x} (loop from PC {:#x} to PC '
                    '{:#x}, branch {} to PC {:#x}). This might cause problems '
                    'with the loop stack and surprising behavior.'.format(
                        pc, loop.start, loop.end, insn.mnemonic, branch_addr))

    return out


def _check_loop_stack(program: OTBNProgram,
                      loops: List[CodeSection]) -> CheckResult:
    '''Checks that loops will likely be properly cleared from loop stack.

    The checks here are based on the OTBN hardware IP documentation on loop
    nesting. From the docs:

        To avoid polluting the loop stack and avoid surprising behaviour, the
        programmer must ensure that:

        * Even if there are branches and jumps within a loop body, the final
          instruction of the loop body gets executed exactly once per
          iteration.

        * Nested loops have distinct end addresses.

        * The end instruction of an outer loop is not executed before an inner
          loop finishes.

    In order to avoid simulating the control flow of the entire program to
    check the first and third conditions, this check takes a conservative,
    simplistic approach and simply warns about all branching into or out of
    loop bodies, including jumps that don't use the call stack (e.g. `jal x0,
    <addr>`). Branching to locations within the same loop body is permitted.

    The second condition in the list, distinct end addresses, is checked
    separately.
    '''
    out = CheckResult()
    out += _check_loop_branching(program, loops)

    # Check that loops have unique end addresses
    end_addrs = []
    for loop in loops:
        if loop.end in end_addrs:
            out.err(
                'Loop starting at PC {:#x} shares a final instruction with '
                'another loop; consider adding a NOP instruction.'.format(
                    loop.start))

    return out


def check_loop(program: OTBNProgram) -> CheckResult:
    '''Check that loops are properly formed.

    Performs three checks to rule out certain classes of loop errors and
    undefined behavior:
    1. For loopi instructions, check that the number of iterations is > 0.
    2. Ensure that loops do not end in control-flow instructions such as jal or
       bne, which will raise LOOP errors.
    3. Checks that there is no branching into or out of loop bodies.
    4. For nested loops, the inner loop is completely contained within the
       outer loop.
    '''
    loops = _get_loops(program)
    out = CheckResult()
    out += _check_loop_iterations(program, loops)
    out += _check_loop_end_insns(program, loops)
    out += _check_loop_stack(program, loops)
    out += _check_loop_inclusion(program, loops)
    out.set_prefix('check_loop: ')
    return out


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument('elf', help=('The .elf file to check.'))
    parser.add_argument('-v', '--verbose', action='store_true')
    args = parser.parse_args()
    program = decode_elf(args.elf)
    result = check_loop(program)
    if args.verbose or result.has_errors() or result.has_warnings():
        print(result.report())
    return 1 if result.has_errors() else 0


if __name__ == "__main__":
    sys.exit(main())
