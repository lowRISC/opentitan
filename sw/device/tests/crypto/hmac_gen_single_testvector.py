#!/usr/bin/env python3
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import argparse
import random
import sys

import hjson
from Crypto.Hash import HMAC, SHA256, SHA384, SHA512

'''
Generate a HMAC/SHA2 vectors for specified sizes.
'''


def validate_inputs(operation, input_msg_len, key_len):
    if operation in ["SHA256", "SHA384", "SHA512"] and key_len != 0:
        raise ValueError("SHA operations should have no key_len inputs")
    if operation in ["HMAC256", "HMAC384", "HMAC512"] and key_len == 0:
        raise ValueError("key_len needs to be larger than 0 for HMAC")
    if input_msg_len % 8 != 0:
        raise ValueError("input_msg_len needs to be divisible by 8")


# Generate a HMAC test vector and return it as string in hjson format.
# The input length arguments are all in bit size.
def gen_random_test(seed, operation, input_msg_len, key_len):

    validate_inputs(operation, input_msg_len, key_len)

    random_instance = random.Random(seed)
    random_instance.seed(seed)
    input_msg = random_instance.randbytes(input_msg_len // 8)
    key = random_instance.randbytes(key_len // 8)

    if operation == "HMAC256":
        mac = HMAC.new(key=key, digestmod=SHA256)
    elif operation == "HMAC384":
        mac = HMAC.new(key=key, digestmod=SHA384)
    elif operation == "HMAC512":
        mac = HMAC.new(key=key, digestmod=SHA512)
    elif operation == "SHA256":
        mac = SHA256.new()
    elif operation == "SHA384":
        mac = SHA384.new()
    elif operation == "SHA512":
        mac = SHA512.new()

    mac.update(input_msg)
    digest = mac.hexdigest()
    vector_identifier = \
        "./sw/device/tests/crypto/hmac_gen_single_testvector.py "\
        "--seed={} --key_len={} --operation={} --input_msg_len={} "\
        "<output-file>"\
        .format(seed, key_len, operation, input_msg_len)

    print(vector_identifier)
    testvec = {
        'vector_identifier': vector_identifier,
        'operation': operation,
        'input_msg': '0x' + input_msg.hex(),
        'digest': '0x' + digest,
    }

    if operation in ["HMAC256", "HMAC384", "HMAC512"]:
        testvec['key'] = '0x' + key.hex()
    return testvec


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--seed',
                        required=True,
                        type=int,
                        help='Seed for randomness.')
    parser.add_argument('--key_len',
                        required=True,
                        type=int,
                        default=0,
                        help='Key length (in bits).')
    parser.add_argument('--operation',
                        required=True,
                        choices=['SHA256', 'SHA384', 'SHA512', 'HMAC256', 'HMAC384', 'HMAC512'],
                        help='SHA/HMAC mode (e.g. SHA256 or HMAC256).')
    parser.add_argument('--input_msg_len',
                        required=True,
                        type=int,
                        help='Input message length (in bits).')
    parser.add_argument('outfile',
                        metavar='FILE',
                        type=argparse.FileType('w'),
                        help='Write output to this file.')

    args = parser.parse_args()

    testvecs = gen_random_test(args.seed, args.operation, args.input_msg_len,
                               args.key_len)

    hjson.dump(testvecs, args.outfile)
    args.outfile.close()

    return 0


if __name__ == '__main__':
    sys.exit(main())
