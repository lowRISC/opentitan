#!/usr/bin/env python3
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import argparse
import random
import sys

import hjson
from Crypto.Hash import KMAC128
from Crypto.Hash import KMAC256

'''
Read in a JSON test vector file, convert the test vector to C constants, and
generate a header file with these test vectors.
'''


def validate_lengths(input_msg_len, cust_str_len, digest_len):
    if input_msg_len % 8 != 0:
        raise ValueError("input_msg_len needs to be divisible by 8")
    # The max length limitation comes from the KMAC HWIP.
    if cust_str_len % 8 != 0 or cust_str_len > 256:
        raise ValueError("cust_str_len needs to be divisible by 8 and not larger than 256 bits")
    # The following is a limitation by the current implementation of KMAC driver
    # function `kmac_kmac_128`, where the digest_len represent number of words
    # but not bytes.
    if digest_len % 32 != 0:
        raise ValueError("digest_len needs to be divisible by 32")


# Generate a KMAC test vector and return it as string in hjson format.
# The input length arguments are all in bit size.
def gen_random_test(seed, key_len, security_str, input_msg_len, cust_str_len,
                    digest_len):

    validate_lengths(input_msg_len, cust_str_len, digest_len)

    random_instance = random.Random(seed)
    random_instance.seed(seed)
    input_msg = random_instance.randbytes(input_msg_len // 8)
    cust_str = random_instance.randbytes(cust_str_len // 8)
    key = random_instance.randbytes(key_len // 8)

    if security_str == 128:
        kmac = KMAC128.new(key = key,
                           data = input_msg,
                           mac_len = digest_len // 8,
                           custom = cust_str)
    elif security_str == 256:
        kmac = KMAC256.new(key = key,
                           data = input_msg,
                           mac_len = digest_len // 8,
                           custom = cust_str)

    digest = kmac.hexdigest()
    vector_identifier = \
        "./sw/device/tests/crypto/kmac_gen_single_testvector.py "\
        "--seed={} --key_len={} --sec_str={} --input_msg_len={} "\
        "--cust_str_len={} --digest_len={} <output-file>"\
        .format(seed, key_len, security_str, input_msg_len,
                cust_str_len, digest_len)

    print(vector_identifier)
    testvec = {
        'vector_identifier': vector_identifier,
        'operation': 'KMAC',
        'security_str': security_str,
        'key': '0x' + key.hex(),
        'input_msg': '0x' + input_msg.hex(),
        'cust_str': '0x' + cust_str.hex(),
        'digest': '0x' + digest,
    }
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
                        choices=[128, 192, 256, 384, 512],
                        help='Key length (in bits).')
    parser.add_argument('--sec_str',
                        required=True,
                        type=int,
                        choices=[128, 256],
                        help='Security strength (either 128 or 256).')
    parser.add_argument('--input_msg_len',
                        required=True,
                        type=int,
                        help='Input message length (in bits).')
    parser.add_argument('--cust_str_len',
                        required=True,
                        type=int,
                        help='Customizatoin string length (in bits).')
    parser.add_argument('--digest_len',
                        required=True,
                        type=int,
                        help='Digest length (in bits).')
    parser.add_argument('outfile',
                        metavar='FILE',
                        type=argparse.FileType('w'),
                        help='Write output to this file.')

    args = parser.parse_args()

    testvecs = gen_random_test(args.seed, args.key_len, args.sec_str,
                               args.input_msg_len, args.cust_str_len,
                               args.digest_len)

    hjson.dump(testvecs, args.outfile)
    args.outfile.close()

    return 0


if __name__ == '__main__':
    sys.exit(main())
