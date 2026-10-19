#!/usr/bin/env python3
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import argparse
import json
import logging
import sys

import jsonschema
from Crypto.PublicKey import ECC
from Crypto.Signature import eddsa
from cryptotest_util import rng

MAX_SIGN_MSG_LEN = 512


def flip_random_bit(buf: bytearray, random_bytes) -> None:
    bit_idx = int.from_bytes(random_bytes(4), "big") % (len(buf) * 8)
    buf[bit_idx // 8] ^= 1 << (bit_idx % 8)


def generate_test_vectors(args):
    test_vectors = []
    random = rng()

    for _ in range(args.count):
        key = ECC.generate(curve="ed25519", randfunc=random)
        private_key = list(key.seed)
        public_key = list(key.public_key().export_key(format="raw"))

        msg_len = int.from_bytes(random(2), "big") % (MAX_SIGN_MSG_LEN + 1)
        msg = random(msg_len)

        signer = eddsa.new(key, "rfc8032")
        sig_bytes = signer.sign(msg)

        test_vectors.append({
            "algorithm": "ed25519",
            "operation": "sign",
            "message": list(msg),
            "public_key": public_key,
            "signature": list(sig_bytes),
            "private_key": private_key,
            "result": True,
        })

        verify_sig = bytearray(sig_bytes)
        verify_result = True
        if random(1)[0] % 2 == 0:
            flip_random_bit(verify_sig, random)
            verify_result = False

        test_vectors.append({
            "algorithm": "ed25519",
            "operation": "verify",
            "message": list(msg),
            "public_key": public_key,
            "signature": list(verify_sig),
            "private_key": [],
            "result": verify_result,
        })

    return test_vectors


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--dst",
        metavar="FILE",
        type=argparse.FileType("w"),
        required=True,
        help="Write output to this file.",
    )
    parser.add_argument(
        "--schema", type=str, required=True, help="Testvector schema file"
    )
    parser.add_argument(
        "--count",
        type=int,
        required=True,
        help="Number of random Ed25519 keys to generate",
    )
    args = parser.parse_args()

    testvecs = generate_test_vectors(args)

    with open(args.schema) as schema_file:
        schema = json.load(schema_file)
    jsonschema.validate(testvecs, schema)

    logging.info(f"Created {len(testvecs)} tests")
    json.dump(testvecs, args.dst)
    args.dst.close()

    return 0


if __name__ == "__main__":
    sys.exit(main())
