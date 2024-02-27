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
from Crypto.Hash import SHA256, SHA384, SHA512, SHA3_256, SHA3_384, SHA3_512
from Crypto.PublicKey import ECC
from Crypto.Signature import DSS
from cryptotest_util import rng

MESSAGE_LENGTH = 512


def generate_test_vectors(args):
    test_vectors = []
    random = rng()
    # Parse tests within the group
    for count in range(args.count):
        # Generate random ECC key pair
        key_pair = ECC.generate(curve=args.curve, randfunc=random)
        public = key_pair.pointQ
        msg = random(MESSAGE_LENGTH)
        signature = []
        # Sign digest of message using private key
        if args.hash_alg == "sha-256":
            digest = SHA256.new(msg)
        elif args.hash_alg == "sha-384":
            digest = SHA384.new(msg)
        elif args.hash_alg == "sha-512":
            digest = SHA512.new(msg)
        elif args.hash_alg == "sha3-256":
            digest = SHA3_256.new(msg)
        elif args.hash_alg == "sha3-384":
            digest = SHA3_384.new(msg)
        elif args.hash_alg == "sha3-512":
            digest = SHA3_512.new(msg)
        else:
            raise ValueError("Unsupported hash algorithm " + args.hash_alg)
        signer = DSS.new(key_pair, 'fips-186-3', randfunc=random)
        signature = signer.sign(digest)

        signature = list(signature)

        verify_result = True
        # Decide whether to flip a bit in the signature, creating a
        # negative test.
        if random(1)[0] % 2 == 0:
            if len(signature) == 0:
                # To change an empty signature, make it a single random byte
                signature = list(random(1))
            else:
                # Flip a random bit in the signature
                idx = int.from_bytes(random(4), "big") % (len(signature) * 8)
                signature[math.floor(idx / 8)] ^= 1 << (idx % 8)
                verify_result = False

        r = signature[:int(len(signature) / 2)]
        s = signature[int(len(signature) / 2):]

        d = hex(int(key_pair.d))[2:]

        # Create sign test vector (currently only SHA-2 is supported)
        if args.hash_alg.startswith("sha-"):
            test_vectors.append({
                "vendor": "random",
                "test_case_id": count,
                "algorithm": "ecdsa",
                "operation": "sign",
                "curve": args.curve,
                "hash_alg": args.hash_alg,
                "message": list(msg),
                # The [2:] removes the '0x' at the beginning of hex strings
                "qx": hex(int(public.x))[2:],
                "qy": hex(int(public.y))[2:],
                "d": d,
                "result": True,
            })

        # Create verify test vector
        test_vectors.append({
            "vendor": "random",
            "test_case_id": count,
            "algorithm": "ecdsa",
            "operation": "verify",
            "curve": args.curve,
            "hash_alg": args.hash_alg,
            "message": list(msg),
            # The [2:] removes the '0x' at the beginning of hex strings
            "qx": hex(int(public.x))[2:],
            "qy": hex(int(public.y))[2:],
            "r": bytes(r).hex(),
            "s": bytes(s).hex(),
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
    parser.add_argument('--count', type=int, help='Number of test vectors to generate')
    parser.add_argument('--curve', type=str, help='Elliptic curve [p256, p384]')
    parser.add_argument('--hash_alg',
                        type=str,
                        help='Hash algorithm \
                        [sha-256, sha-384, sha-512, sha3-256, sha3-384, sha3-512]')
    args = parser.parse_args()

    testvecs = generate_test_vectors(args)

    # Validate generated JSON
    with open(args.schema) as schema_file:
        schema = json.load(schema_file)
    jsonschema.validate(testvecs, schema)

    logging.info(f"Created {len(testvecs)} tests")
    json.dump(testvecs, args.dst)
    args.dst.close()

    return 0


if __name__ == '__main__':
    sys.exit(main())
