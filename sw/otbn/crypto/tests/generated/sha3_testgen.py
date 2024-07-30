#!/usr/bin/env python3
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import argparse
import random
from typing import TextIO, Optional

from Crypto.Hash import SHA3_224, SHA3_256, SHA3_384, SHA3_512

from shared.testgen import write_test_data, write_test_exp

DST_LEN = random.choice([28, 32, 48, 64])  # 28, 32, 48, 64
MSG_LEN_UBOUND = 512  # change this to set upper bound for message's length


def gen_sha3_test(seed: Optional[int], data_file: TextIO, exp_file: TextIO):
    # Generate random operands.
    if seed is not None:
        random.seed(seed)
    msg_len = random.randint(0, MSG_LEN_UBOUND)
    msg = random.getrandbits(8 * msg_len)
    dst_len_bytes = int.to_bytes(DST_LEN, byteorder='little', length=32)
    msg_len_bytes = int.to_bytes(msg_len, byteorder='little', length=32)
    msg_bytes = int.to_bytes(msg, byteorder='little', length=msg_len)

    # Write input values.
    inputs = {'dst_len': dst_len_bytes, 'msg': msg_bytes, 'msg_len': msg_len_bytes}
    write_test_data(inputs, data_file)

    # Compute SHA3-{DST_LEN}.
    if DST_LEN == 28:
        dst_ref = SHA3_224.new()
    elif DST_LEN == 32:
        dst_ref = SHA3_256.new()
    elif DST_LEN == 48:
        dst_ref = SHA3_384.new()
    else:
        dst_ref = SHA3_512.new()
    dst_ref.update(msg_bytes)

    # Write expected output values.
    exp = {}
    for i in range(2):
        exp[f'w{i}'] = dst_ref.digest()[32 * i: 32 * (i + 1)]
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
    gen_sha3_test(args.seed, args.data, args.exp)
