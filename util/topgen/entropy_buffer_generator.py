#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""Entropy Buffer Generator

Creates an array of random bytes and stores it in a file.
Typical usage:

./entropy_buffer_generator.py -n 100

This will create a file 'entropy_buffer.npy' consisting of 100 bytes.
"""
import argparse

import logging as log
import numpy as np
import random
import secrets
import sys


def parse_args():
    """Parses command-line arguments."""
    parser = argparse.ArgumentParser(
        description="""The Entropy Buffer file-generator.
        Randomness is generated using random.py
        This randomness is not cryptographic-strength and should be only used
        for tests.
        """)
    parser.add_argument("-o",
                        "--output-file",
                        default='entropy_buffer.txt',
                        help="entropy buffer file name")
    parser.add_argument("-n",
                        "--num-bytes",
                        type=int,
                        default=16,
                        help="""number of bytes to generate""")
    parser.add_argument("--sec",
                        action="store_true",
                        default=False,
                        help="""Generate random numbers from the most secure
                        source of randomness the OS provides. Cannot be used
                        together with --seed.""")
    parser.add_argument("-s",
                        "--seed",
                        type=int,
                        help="""Custom seed for RNG to generate the entropy
                        buffer. Cannot be used if sec = True.""")
    return parser.parse_args()


def main():

    args = parse_args()
    k = args.num_bytes
    out = args.output_file
    sec = args.sec
    seed = args.seed

    if (sec and seed):
        log.error("Options --sec and --seed cannot be used together")
        sys.exit(1)

    if not (sec or seed):
        seed = random.getrandbits(64)
        log.warning("No seed specified, setting to {}.".format(seed))

    buffer = np.zeros(k, dtype='uint8')
    if sec:
        for i in range(k):
            buffer[i] = secrets.randbelow(256)
    else:
        random.seed(seed)
        for i in range(k):
            buffer[i] = random.getrandbits(8)

    np.savetxt(out, buffer, fmt='%d')


if __name__ == "__main__":
    main()
