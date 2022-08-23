#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

'''Run a test on the OTBN simulator.'''

import argparse
import subprocess
import sys

from shared.check import CheckResult
from shared.reg_dump import parse_reg_dump

# Names of special registers
ERR_BITS = 'ERR_BITS'
INSN_CNT = 'INSN_CNT'
STOP_PC = 'STOP_PC'


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
            result.err(f'OTBN encountered an unexpected error.\n'
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
