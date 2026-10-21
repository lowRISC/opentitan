#!/usr/bin/env python3
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import argparse
import json
import logging
import sys

import jsonschema
from Crypto.Hash import KMAC128, KMAC256, SHA256, SHA384, SHA512
from Crypto.Protocol.KDF import HKDF
from cryptotest_util import rng

MAX_KEY_BYTES = 192
MAX_LABEL_BYTES = 192
MAX_CONTEXT_BYTES = 256
MAX_OUTPUT_BYTES = 256

KMAC_MAX_LABEL_BYTES = 32
KMAC_MIN_OUTPUT_BYTES = 8
KMAC128_KEY_LENGTHS = (16, 24, 32, 48, 64)
KMAC256_KEY_LENGTHS = (32, 48, 64)

HKDF_HASH_MAP = {
    "sha-256": SHA256,
    "sha-384": SHA384,
    "sha-512": SHA512,
}

KMAC_MAP = {
    "kmac-128": (KMAC128, KMAC128_KEY_LENGTHS),
    "kmac-256": (KMAC256, KMAC256_KEY_LENGTHS),
}


def flip_random_bit(buf: bytearray, random_bytes) -> None:
    bit_idx = int.from_bytes(random_bytes(4), "big") % (len(buf) * 8)
    buf[bit_idx // 8] ^= 1 << (bit_idx % 8)


def generate_test_vectors(args):
    test_vectors = []
    random = rng()

    for count in range(args.count):
        if args.algorithm == "hkdf":
            if args.mode not in HKDF_HASH_MAP:
                raise ValueError(f"Unsupported HKDF mode: {args.mode}")
            hash_mod = HKDF_HASH_MAP[args.mode]

            key_len = 1 + (int.from_bytes(random(2), "big") % MAX_KEY_BYTES)
            label_len = int.from_bytes(random(2), "big") % (MAX_LABEL_BYTES + 1)
            context_len = int.from_bytes(random(2), "big") % (MAX_CONTEXT_BYTES + 1)
            output_len = 1 + (int.from_bytes(random(2), "big") % MAX_OUTPUT_BYTES)

            key = random(key_len)
            label = random(label_len)
            context = random(context_len)

            output = HKDF(
                master=key,
                key_len=output_len,
                salt=label,
                hashmod=hash_mod,
                num_keys=1,
                context=context,
            )
        elif args.algorithm == "kmac-kdf":
            if args.mode not in KMAC_MAP:
                raise ValueError(f"Unsupported KMAC-KDF mode: {args.mode}")
            kmac_mod, key_lengths = KMAC_MAP[args.mode]

            key_len = key_lengths[random(1)[0] % len(key_lengths)]
            label_len = int.from_bytes(random(2), "big") % (KMAC_MAX_LABEL_BYTES + 1)
            context_len = int.from_bytes(random(2), "big") % (MAX_CONTEXT_BYTES + 1)
            output_len = KMAC_MIN_OUTPUT_BYTES + (
                int.from_bytes(random(2), "big")
                % (MAX_OUTPUT_BYTES - KMAC_MIN_OUTPUT_BYTES + 1)
            )

            key = random(key_len)
            label = random(label_len)
            context = random(context_len)

            h = kmac_mod.new(
                key=key,
                data=context,
                mac_len=output_len,
                custom=label,
            )
            output = h.digest()
        else:
            raise ValueError(f"Unsupported KDF algorithm: {args.algorithm}")

        output_buf = bytearray(output)
        result = True
        if random(1)[0] % 2 == 0:
            flip_random_bit(output_buf, random)
            result = False

        test_vectors.append({
            "vendor": "random",
            "test_case_id": count,
            "algorithm": args.algorithm,
            "mode": args.mode,
            "key": list(key),
            "label": list(label),
            "context": list(context),
            "output": list(output_buf),
            "result": result,
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
        help="Number of random KDF test vectors to generate",
    )
    parser.add_argument(
        "--algorithm",
        type=str,
        required=True,
        choices=["hkdf", "kmac-kdf"],
        help="KDF algorithm",
    )
    parser.add_argument(
        "--mode",
        type=str,
        required=True,
        choices=["sha-256", "sha-384", "sha-512", "kmac-128", "kmac-256"],
        help="Underlying PRF mode",
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
