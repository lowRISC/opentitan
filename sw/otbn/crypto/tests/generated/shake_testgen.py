#!/usr/bin/env python3
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import argparse
import random
from typing import TextIO, Optional

from Crypto.Hash import SHAKE128, SHAKE256

from shared.testgen import write_test_data, write_test_exp

DST_LEN = random.choice([16, 32])  # SHAKE128: 16, SHAKE256: 32
MSG_LEN_UBOUND = 512  # change this to set upper bound for message's length
DST_SQUEEZE_BOUND = 32  # change this to set upper bound for SHAKE squeeze


def gen_shake_test(seed: Optional[int], data_file: TextIO, exp_file: TextIO):
    # Generate random operands.
    if seed is not None:
        random.seed(seed)
    msg_len = random.randint(0, MSG_LEN_UBOUND)
    dst_squeeze = random.randint(1, DST_SQUEEZE_BOUND)
    msg = random.getrandbits(8 * msg_len)
    dst_len_bytes = int.to_bytes(DST_LEN, byteorder='little', length=32)
    msg_len_bytes = int.to_bytes(msg_len, byteorder='little', length=32)
    msg_bytes = int.to_bytes(msg, byteorder='little', length=msg_len)
    dst_squeeze_bytes = int.to_bytes(dst_squeeze, byteorder='little', length=32)

    # Write input values.
    inputs = {
        'dst_len': dst_len_bytes,
        'msg': msg_bytes,
        'msg_len': msg_len_bytes,
        'dst_squeeze': dst_squeeze_bytes
    }
    write_test_data(inputs, data_file)

    # Compute reference SHAKE.
    if DST_LEN == 16:
        dst_ref = SHAKE128.new()
    else:
        dst_ref = SHAKE256.new()
    dst_ref.update(msg_bytes)
    for i in range(dst_squeeze - 1):
        dst_ref.read(32)

    # Write expected output values.
    exp = {}
    exp['w0'] = dst_ref.read(32)
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
    gen_shake_test(args.seed, args.data, args.exp)
