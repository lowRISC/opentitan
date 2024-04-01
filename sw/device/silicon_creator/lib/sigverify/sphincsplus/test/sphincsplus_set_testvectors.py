#!/usr/bin/env python3
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import argparse
import sys

import hjson
from mako.template import Template

'''
Read in an HJSON test vector file, convert the test vector to C constants, and
generate a header file with these test vectors.
'''


def hex_to_hexbytes(x):
    '''Convert a hex string to a list of bytes as hex strings.'''
    if x.startswith('0x'):
        x = x[2:]

    # Double-check that length is even
    if len(x) % 2 != 0:
        raise ValueError(f'Cannot convert odd-length hex string (length {len(x)}) to bytes: {x}')

    out = []
    for i in range(0, len(x), 2):
        out.append('0x' + x[i:i + 2])
    return out


def hex_to_hexwords(x):
    '''Convert a hex string little-endian 32-bit words as hex strings.'''
    if x.startswith('0x'):
        x = x[2:]

    # Double-check that length is divisible by 8.
    if len(x) % 8 != 0:
        raise ValueError(f'Hex string with length {len(x)} is not divisible by'
                         f'word size (32 bits): {x}')

    out = []
    for i in range(0, len(x), 8):
        # Reverse the order of bytes in each word.
        word = '0x'
        for j in range(i + 8, i, -2):
            word += x[j - 2:j]
        out.append(word)
    return out


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument('--hjsonfile', '-j',
                        metavar='FILE',
                        required=True,
                        type=argparse.FileType('r'),
                        help='Read test vectors from this HJSON file.')
    parser.add_argument('--template', '-t',
                        metavar='FILE',
                        required=True,
                        type=argparse.FileType('r'),
                        help='Read header template from this file.')
    parser.add_argument('--headerfile', '-o',
                        metavar='FILE',
                        required=True,
                        type=argparse.FileType('w'),
                        help='Write output to this file.')

    args = parser.parse_args()

    # Read test vectors and stringify them
    with args.hjsonfile as hjsonfile:
        testvecs = hjson.load(hjsonfile)

    # Convert the values to hexadecimal bytes.
    for t in testvecs:
        t['sig_hexwords'] = hex_to_hexwords(t['sig_hex'])
        t['msg_hexbytes'] = hex_to_hexbytes(t['msg_hex'])
        t['pk_hexwords'] = hex_to_hexwords(t['pk_hex'])

    with args.template as template:
        with args.headerfile as header:
            header.write(Template(template.read()).render(tests=testvecs))

    return 0


if __name__ == '__main__':
    sys.exit(main())
