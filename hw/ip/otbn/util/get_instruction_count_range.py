#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import argparse

from shared.decode import decode_elf
from shared.instruction_count_range import (program_insn_count_range,
                                            subroutine_insn_count_range)


def main() -> int:
    parser = argparse.ArgumentParser(description=(
        'Get the range of possible instruction counts for an OTBN program or '
        'across all valid control-flow paths. At runtime, one can read the '
        'instruction count register and make sure the values fall within this '
        'range to protect against certain fault injection attacks.'))
    parser.add_argument('elf', help=('The .elf file to check.'))
    parser.add_argument(
        '--subroutine',
        required=False,
        help=('The specific subroutine to check. If not provided, the start '
              'point is _imem_start (whole program).'))
    args = parser.parse_args()
    program = decode_elf(args.elf)

    # Compute instruction count range.
    if args.subroutine is None:
        min_count, max_count = program_insn_count_range(program)
    else:
        min_count, max_count = subroutine_insn_count_range(
            program, args.subroutine)

    # Print results.
    print(f'Minimum instruction count: {min_count}')
    if max_count is None:
        print('Maximum instruction count could not be calculated.')
    else:
        print(f'Maximum instruction count: {max_count}')


if __name__ == "__main__":
    main()
