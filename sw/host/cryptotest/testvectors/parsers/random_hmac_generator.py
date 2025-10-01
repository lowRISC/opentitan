#!/usr/bin/env python3
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import argparse
import json
import logging
import math
import sys

import jsonschema
from Crypto.Hash import SHA, SHA224, SHA256, SHA384, SHA512, SHA3_256, SHA3_384, SHA3_512
from Crypto.Hash import HMAC
from cryptotest_util import rng

MESSAGE_LENGTH = 256
DEFAULT_KEY_LENGTH = 256  # bits
MIN_KEY_LENGTH = 64  # bits
MAX_KEY_LENGTH = 2048  # bits


def generate_test_vectors(args):
    test_vectors = []
    random = rng()

    # Parse tests within the group
    for count in range(args.count):
        # Generate random key
        key_bytes = args.key_length // 8
        if args.key_length % 8 != 0:
            logging.warning(f"Key length {args.key_length} is not a multiple of 8. "
                            f"Generating {key_bytes + 1} bytes for the key.")
            key = random(key_bytes + 1)
        else:
            key = random(key_bytes)

        msg_len = int.from_bytes(random(4), byteorder='big', signed=False) % (MESSAGE_LENGTH + 1)
        msg = random(msg_len)
        tag = []

        # Create HMAC object based on the hash algorithm
        if args.hash_alg == "sha-1":
            h_alg = SHA
        elif args.hash_alg == "sha-224":
            h_alg = SHA224
        elif args.hash_alg == "sha-256":
            h_alg = SHA256
        elif args.hash_alg == "sha-384":
            h_alg = SHA384
        elif args.hash_alg == "sha-512":
            h_alg = SHA512
        elif args.hash_alg == "sha3-256":
            h_alg = SHA3_256
        elif args.hash_alg == "sha3-384":
            h_alg = SHA3_384
        elif args.hash_alg == "sha3-512":
            h_alg = SHA3_512
        else:
            raise ValueError(f"Unsupported hash algorithm {args.hash_alg}")

        h_mac = HMAC.new(key, digestmod=h_alg)
        h_mac.update(msg)
        tag = h_mac.digest()

        verify_result = True
        # Decide whether to flip a bit in the tag, creating a
        # negative test.
        if random(1)[0] % 2 == 0:
            if len(tag) == 0:
                # To change an empty tag, make it a single random byte
                tag = random(1)
            else:
                # Flip a random bit in the tag
                tag_list = list(tag)  # Convert bytes to list for mutability
                idx = int.from_bytes(random(4), "big") % (len(tag_list) * 8)
                tag_list[math.floor(idx / 8)] ^= 1 << (idx % 8)
                tag = bytes(tag_list)  # Convert back to bytes
                verify_result = False

        test_vectors.append({
            "vendor": "random",
            "test_case_id": count,
            "algorithm": "hmac",
            "hash_alg": args.hash_alg,
            "key": list(key),
            "message": list(msg),
            "tag": list(tag),
            "result": verify_result,
        })

    return test_vectors


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--dst',
                        metavar='FILE',
                        type=argparse.FileType('w'),
                        help='Write output to this file.')
    parser.add_argument('--schema', type=str, help='Testvector schema file')
    parser.add_argument('--count',
                        type=int,
                        help='Number of test vectors to generate',
                        required=True)
    parser.add_argument('--key_length',
                        type=int,
                        default=DEFAULT_KEY_LENGTH,
                        help=f'Key length in bits [{MIN_KEY_LENGTH}-{MAX_KEY_LENGTH}]')
    parser.add_argument('--hash_alg',
                        type=str,
                        help=('Hash algorithm [sha-1, sha-224, sha-256, sha-384, '
                              'sha-512, sha3-256, sha3-384, sha3-512]'),
                        required=True)
    args = parser.parse_args()

    if not (MIN_KEY_LENGTH <= args.key_length <= MAX_KEY_LENGTH):
        parser.error(f"Key length must be between {MIN_KEY_LENGTH} and {MAX_KEY_LENGTH} bits.")

    testvecs = generate_test_vectors(args)

    # Validate generated JSON
    if args.schema:
        with open(args.schema) as schema_file:
            schema = json.load(schema_file)
        jsonschema.validate(testvecs, schema)

    logging.info(f"Created {len(testvecs)} tests")
    json.dump(testvecs, args.dst, indent=2)  # Use indent for better readability
    args.dst.close()

    return 0


if __name__ == '__main__':
    sys.exit(main())
