#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import argparse
import sys
from typing import Dict, Tuple

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


def check_call_stack(program: OTBNProgram) -> Tuple[bool, str]:
    '''Check that the special register x1 is used safely.

    If x1 is used for purposes unrelated to the call stack, it can trigger a
    CALL_STACK error. This check errors if x1 is used for any other instruction
    than `jal` or `jalr`.
    '''
    for pc in program.insns:
        insn = program.get_insn(pc)
        operands = program.get_operands(pc)
        if not _check_call_stack_insn(insn, operands):
            return (False, 'check_call_stack: FAIL at PC {:#x}: {} {}'.format(
                pc, insn.mnemonic, operands))
    return (True, 'check_call_stack: PASS')


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument('elf', help=('The .elf file to check.'))
    args = parser.parse_args()
    program = decode_elf(args.elf)
    ok, msg = check_call_stack(program)
    print(msg)
    if not ok:
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
