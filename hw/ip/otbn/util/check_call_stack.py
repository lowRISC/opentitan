#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import argparse
import sys
from typing import Dict

from shared.check import CheckResult
from shared.decode import OTBNProgram, decode_elf
from shared.insn_yaml import Insn
from shared.operand import RegOperandType


def _check_call_stack_insn(insn: Insn, operands: Dict[str, int]) -> bool:
    '''Returns false if the instruction uses x1 and is not `jal`/`jalr`.'''
    if insn.mnemonic in ['jal', 'jalr']:
        # JAL and JALR instructions are allowed to use x1.
        return True

    # For all gpr operands, check that they are not x1.
    for op in insn.operands:
        if isinstance(op.op_type,
                      RegOperandType) and op.op_type.reg_type == 'gpr':
            if operands[op.name] == 1:
                return False

    return True


def check_call_stack(program: OTBNProgram) -> CheckResult:
    '''Check that the special register x1 is used safely.

    If x1 is used for purposes unrelated to the call stack, it can trigger a
    CALL_STACK error. This check errors if x1 is used for any other instruction
    than `jal` or `jalr`.
    '''
    out = CheckResult()
    for pc, (insn, operands) in program.insns.items():
        if not _check_call_stack_insn(insn, operands):
            out.err(
                'Potentially dangerous use of the call stack register x1 at '
                'PC {:#x}: {}'.format(pc, insn.disassemble(pc, operands)))
    out.set_prefix('check_call_stack: ')
    return out


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument('elf', help=('The .elf file to check.'))
    parser.add_argument('-v', '--verbose', action='store_true')
    args = parser.parse_args()
    program = decode_elf(args.elf)
    result = check_call_stack(program)
    if args.verbose or result.has_errors() or result.has_warnings():
        print(result.report())
    return 1 if result.has_errors() else 0


if __name__ == "__main__":
    sys.exit(main())
