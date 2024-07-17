#!/usr/bin/env python3
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import argparse
import random
from typing import TextIO, Optional

from shared.testgen import write_test_data, write_test_exp

OPERAND_LIMBS = 2
LIMB_NBYTES = 32


def gen_mul_test(seed: Optional[int], data_file: TextIO, exp_file: TextIO):
    # Generate random operands.
    if seed is not None:
        random.seed(seed)
    operand_nbytes = LIMB_NBYTES * OPERAND_LIMBS
    x = random.getrandbits(8 * operand_nbytes)
    y = random.getrandbits(8 * operand_nbytes)
    x_bytes = int.to_bytes(x, byteorder='little', length=operand_nbytes)
    y_bytes = int.to_bytes(y, byteorder='little', length=operand_nbytes)

    # Write input values.
    inputs = {'x': x_bytes, 'y': y_bytes}
    write_test_data(inputs, data_file)

    # Write expected output values.
    xy_bytes = int.to_bytes(x * y, byteorder='little', length=operand_nbytes * 2)
    exp = {}
    for i in range(OPERAND_LIMBS * 2):
        exp[f'w{i}'] = xy_bytes[i * LIMB_NBYTES:(i + 1) * LIMB_NBYTES]
    write_test_exp(exp, exp_file)


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('-s', '--seed',
                        type=int,
                        required=False,
                        help=('Seed value for pseudorandomness.'))
    parser.add_argument('data',
                        metavar='FILE',
                        type=argparse.FileType('w'),
                        help=('Output file for input DMEM values.'))
    parser.add_argument('exp',
                        metavar='FILE',
                        type=argparse.FileType('w'),
                        help=('Output file for expected register values.'))
    args = parser.parse_args()

    gen_mul_test(args.seed, args.data, args.exp)
