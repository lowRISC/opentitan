#!/usr/bin/env python3
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import argparse
import random
import sys

import hjson
import kmac_gen_single_testvector
'''
Read in a JSON test vector file, convert the test vector to C constants, and
generate a header file with these test vectors.
'''


def gen_random_test(idx):
    random_instance = random.Random(idx)
    security_str = random_instance.choice([128, 256])
    input_msg_len = 8 * random_instance.randint(0, 20)
    cust_str_len = 8 * random_instance.randint(0, 32)
    # Ensure that the key length is larger or equal to security parameter.
    # Also, KMAC HWIP only supports a discrete set of key lengths.
    if security_str == 128:
        key_len = random_instance.choice([128, 192, 256, 384, 512])
    else:
        key_len = random_instance.choice([256, 384, 512])

    # Due to current KMAC driver limitation, only multiples of 32-bit are
    # allowed.
    digest_len = 32 * random_instance.randint(2, 16)

    return kmac_gen_single_testvector.gen_random_test(idx, key_len, security_str,
                                                      input_msg_len, cust_str_len, digest_len)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('n',
                        type=int,
                        help='Number of random test vectors to generate.')
    parser.add_argument('outfile',
                        metavar='FILE',
                        type=argparse.FileType('w'),
                        help='Write output to this file.')

    args = parser.parse_args()

    testvecs = []
    for i in range(args.n):
        testvecs.append(gen_random_test(i))

    hjson.dump(testvecs, args.outfile)
    args.outfile.close()

    return 0


if __name__ == '__main__':
    sys.exit(main())
