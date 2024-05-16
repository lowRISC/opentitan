#!/usr/bin/env python3
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import argparse
import random
import sys

import hjson
import hmac_gen_single_testvector
'''
Generate multiple test vectos
'''


def gen_random_test(idx):
    random_instance = random.Random(idx)
    operation = random_instance.choice(["SHA256", "HMAC256", "SHA384", "HMAC384",
                                        "SHA512", "HMAC512"])
    input_msg_len = 8 * random_instance.randint(0, 1000)
    # Ensure that the key length is larger or equal to security parameter.
    # Also, KMAC HWIP only supports a discrete set of key lengths.
    if operation[0:4] == "HMAC":
        key_len = 8 * random_instance.randint(80, 256)
    else:
        key_len = 0

    return hmac_gen_single_testvector.gen_random_test(idx, operation, input_msg_len, key_len)


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
