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

import numpy as np
import random


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
    return parser.parse_args()


def main():

    args = parse_args()
    k = args.num_bytes
    out = args.output_file

    buffer = np.zeros(k, dtype='uint8')
    for i in range(k):
        buffer[i] = random.getrandbits(8)

    np.savetxt(out, buffer, fmt='%d')


if __name__ == "__main__":
    main()
