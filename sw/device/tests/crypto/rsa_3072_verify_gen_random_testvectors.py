#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import argparse
import random
import sys

import hjson
from Crypto.Hash import SHA256
from Crypto.PublicKey import RSA
from Crypto.Signature import pkcs1_15


def gen_random_test(key, idx):
    # Generate a random message with length between 0 and 1000 bytes
    msg_len = random.randint(0, 1000)
    msg_bytes = random.randbytes(msg_len)
    msg = int.from_bytes(msg_bytes, byteorder='big')

    # Decide randomly whether to generate a valid or invalid signature
    valid = random.choice([True, False])

    if valid:
        h = SHA256.new(msg_bytes)
        signature_bytes = pkcs1_15.new(key).sign(h)
    else:
        # Generate a random 3072-bit signature
        signature_bytes = random.randbytes(int(3072 / 8))
        comment = 'Randomly-generated test vector (id={}) with invalid signature'.format(
            idx)

    signature = int.from_bytes(signature_bytes, byteorder='big')

    testvec = {
        'n': key.n,
        'e': key.e,
        'msg': msg,
        'msg_len': msg_len,
        'signature': signature,
        'valid': valid,
    }

    # Set the comment to print the whole test vector (so failures can be
    # replicated)
    comment = 'Randomly-generated test vector (id={}):'.format(idx)
    comment += ', '.join('{}: {}'.format(k, v) for k, v in testvec.items())
    testvec['comment'] = comment

    return testvec


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--verbose', action='store_true')
    parser.add_argument('n',
                        type=int,
                        help='Number of random test vectors to generate.')
    parser.add_argument('--tests-per-key',
                        metavar='num',
                        type=int,
                        required=False,
                        default=5,
                        help='Number of test vectors to generate per key '
                        'generation (default=5). Increase for faster test '
                        'generation, and decrease for more coverage.')
    parser.add_argument('outfile',
                        metavar='FILE',
                        type=argparse.FileType('w'),
                        help='Write output to this file.')

    args = parser.parse_args()

    random.seed()
    testvecs = []
    key = None
    for i in range(args.n):
        if args.verbose:
            print('Generating test case {}'.format(i))

        if i % args.tests_per_key == 0:
            # Generate a new RSA key
            key = RSA.generate(3072, e=65537)

        testvecs.append(gen_random_test(key, i))

    hjson.dump(testvecs, args.outfile)
    args.outfile.close()

    return 0


if __name__ == '__main__':
    sys.exit(main())
