#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import argparse
import sys

import hjson
from mako.template import Template

'''
Read in a JSON test vector file, convert the test vector to C constants, and
generate a header file with these test vectors.
'''

# Number of 32-bit words in a 3072-bit number
RSA_3072_NUMWORDS = int(3072 / 32)


def rsa_3072_int_to_hexwords(x):
    '''Convert a 3072-bit integer to a list of 32-bit integers (little-endian).'''
    out = []
    for _ in range(RSA_3072_NUMWORDS):
        out.append(x & ((1 << 32) - 1))
        x >>= 32
    # Note: some test sets may contain (invalid) signatures that are > 3072
    # words. The type signature of our RSA-3072 implementation rules out
    # getting the full value as input, so they are truncated here.
    return ['{:#010x}'.format(w) for w in out]


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
    testvecs = hjson.load(args.hjsonfile)
    args.hjsonfile.close()

    # Convert the 3072-bit numbers n and sig into words expressed in hex
    for t in testvecs:
        t['n_hexwords'] = rsa_3072_int_to_hexwords(t['n'])
        t['sig_hexwords'] = rsa_3072_int_to_hexwords(t['signature'])

    # Convert the message into an array of bytes
    for t in testvecs:
        t['msg_bytes'] = t['msg'].to_bytes(t['msg_len'], byteorder='big')

    tpl = Template(args.template.read())
    args.headerfile.write(tpl.render(tests=testvecs))
    args.headerfile.close()
    args.template.close()

    return 0


if __name__ == '__main__':
    sys.exit(main())
