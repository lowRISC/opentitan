#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

'''Run a test on the OTBN simulator.'''

import argparse
import subprocess
import sys
from enum import IntEnum
from typing import List

from shared.check import CheckResult
from shared.reg_dump import parse_reg_dump

# Names of special registers
ERR_BITS = 'ERR_BITS'
INSN_CNT = 'INSN_CNT'
STOP_PC = 'STOP_PC'


# copied from hw/ip/otbn/dv/otbnsim/sim/constants.py
class ErrBits(IntEnum):
    '''A copy of the list of bits in the ERR_BITS register.'''
    BAD_DATA_ADDR = 1 << 0
    BAD_INSN_ADDR = 1 << 1
    CALL_STACK = 1 << 2
    ILLEGAL_INSN = 1 << 3
    LOOP = 1 << 4
    KEY_INVALID = 1 << 5
    RND_REP_CHK_FAIL = 1 << 6
    RND_FIPS_CHK_FAIL = 1 << 7
    IMEM_INTG_VIOLATION = 1 << 16
    DMEM_INTG_VIOLATION = 1 << 17
    REG_INTG_VIOLATION = 1 << 18
    BUS_INTG_VIOLATION = 1 << 19
    BAD_INTERNAL_STATE = 1 << 20
    ILLEGAL_BUS_ACCESS = 1 << 21
    LIFECYCLE_ESCALATION = 1 << 22
    FATAL_SOFTWARE = 1 << 23


def get_err_names(err: int) -> List[str]:
    '''Get the names of all error bits that are set.'''
    out = []
    for err_bit in ErrBits:
        if err & err_bit != 0:
            out.append(err_bit.name)
    return out


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument('simulator',
                        help='Path to the standalone OTBN simulator.')
    parser.add_argument('expected',
                        metavar='FILE',
                        type=argparse.FileType('r'),
                        help=(f'File containing expected register values. '
                              f'Registers that are not listed are allowed to '
                              f'have any value, except for {ERR_BITS}. If '
                              f'{ERR_BITS} is not listed, the test will assume '
                              f'there are no errors expected (i.e. {ERR_BITS}'
                              f'= 0).'))
    parser.add_argument('elf',
                        help='Path to the .elf file for the OTBN program.')
    parser.add_argument('-v', '--verbose', action='store_true')
    args = parser.parse_args()

    # Parse expected values.
    result = CheckResult()
    expected_regs = parse_reg_dump(args.expected.read())

    # Run the simulation and produce a register dump.
    cmd = [args.simulator, '--dump-regs', '-', args.elf]
    sim_proc = subprocess.run(cmd, check=True,
                              stdout=subprocess.PIPE, universal_newlines=True)
    actual_regs = parse_reg_dump(sim_proc.stdout)

    # Special handling for the ERR_BITS register.
    expected_err = expected_regs.get(ERR_BITS, 0)
    actual_err = actual_regs[ERR_BITS]
    insn_cnt = actual_regs[INSN_CNT]
    stop_pc = actual_regs[STOP_PC]
    if expected_err == 0 and actual_err != 0:
        # Test is expected to have no errors, but an error occurred. In this
        # case, give a special error message and exit rather than print all the
        # mismatched registers.
        if actual_err != 0:
            err_names = ', '.join(get_err_names(actual_err))
            result.err(f'OTBN encountered an unexpected error: {err_names}.\n'
                       f'  {ERR_BITS}\t= {actual_err:#010x}\n'
                       f'  {INSN_CNT}\t= {insn_cnt:#010x}\n'
                       f'  {STOP_PC}\t= {stop_pc:#010x}')
    else:
        for reg, expected_value in expected_regs.items():
            actual_value = actual_regs.get(reg, None)
            if actual_value != expected_value:
                if reg.startswith('w'):
                    expected_str = f'{expected_value:#066x}'
                    actual_str = f'{actual_value:#066x}'
                else:
                    expected_str = f'{expected_value:#010x}'
                    actual_str = f'{actual_value:#010x}'
                result.err(f'Mismatch for register {reg}:\n'
                           f'  Expected: {expected_str}\n'
                           f'  Actual:   {actual_str}')

    if result.has_errors() or result.has_warnings() or args.verbose:
        print(result.report())

    return 1 if result.has_errors() else 0


if __name__ == "__main__":
    sys.exit(main())
