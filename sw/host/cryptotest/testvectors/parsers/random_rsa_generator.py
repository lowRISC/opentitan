#!/usr/bin/env python3
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import argparse
import json
import logging
import sys

import jsonschema
from Crypto.Cipher import PKCS1_OAEP
from Crypto.Hash import SHA256, SHA384, SHA512, SHA3_256, SHA3_384, SHA3_512
from Crypto.PublicKey import RSA
from Crypto.Signature import pkcs1_15, pss
from cryptotest_util import rng

RSA_E = 65537
MAX_SIGN_MSG_LEN = 512
MAX_OAEP_LABEL_LEN = 64

HASH_ALGS = {
    "sha-256": SHA256,
    "sha-384": SHA384,
    "sha-512": SHA512,
    "sha3-256": SHA3_256,
    "sha3-384": SHA3_384,
    "sha3-512": SHA3_512,
}


def flip_random_bit(buf: bytearray, random_bytes) -> None:
    bit_idx = int.from_bytes(random_bytes(4), "big") % (len(buf) * 8)
    buf[bit_idx // 8] ^= 1 << (bit_idx % 8)


def generate_test_vectors(args):
    test_vectors = []
    random = rng()

    if args.hash_alg not in HASH_ALGS:
        raise ValueError(f"Unsupported hash algorithm: {args.hash_alg}")
    hash_mod = HASH_ALGS[args.hash_alg]

    n_bytes = args.security_level // 8
    tc_id = 1

    for _ in range(args.count):
        key = RSA.generate(bits=args.security_level, randfunc=random, e=RSA_E)
        n_bytes_list = list(int(key.n).to_bytes(n_bytes, "big"))
        d_bytes_list = list(int(key.d).to_bytes(n_bytes, "big"))

        if args.padding in ("pkcs1_1.5", "pss"):
            msg_len = int.from_bytes(random(2), "big") % (MAX_SIGN_MSG_LEN + 1)
            msg = random(msg_len)
            digest = hash_mod.new(msg)

            if args.padding == "pkcs1_1.5":
                signer = pkcs1_15.new(key)
                sig_bytes = signer.sign(digest)
            else:
                signer = pss.new(
                    key, salt_bytes=digest.digest_size, rand_func=random
                )
                sig_bytes = signer.sign(digest)

            sign_vec = {
                "vendor": "random",
                "test_case_id": tc_id,
                "algorithm": "rsa",
                "operation": "sign",
                "padding": args.padding,
                "security_level": args.security_level,
                "hash_alg": args.hash_alg,
                "message": list(msg),
                "n": n_bytes_list,
                "e": int(key.e),
                "d": d_bytes_list,
                "label": [],
                "result": True,
            }
            if args.padding == "pkcs1_1.5":
                sign_vec["signature"] = list(sig_bytes)
            test_vectors.append(sign_vec)
            tc_id += 1

            verify_sig = bytearray(sig_bytes)
            verify_result = True
            if random(1)[0] % 2 == 0:
                flip_random_bit(verify_sig, random)
                verify_result = False

            test_vectors.append({
                "vendor": "random",
                "test_case_id": tc_id,
                "algorithm": "rsa",
                "operation": "verify",
                "padding": args.padding,
                "security_level": args.security_level,
                "hash_alg": args.hash_alg,
                "message": list(msg),
                "n": n_bytes_list,
                "e": int(key.e),
                "signature": list(verify_sig),
                "result": verify_result,
            })
            tc_id += 1

        elif args.padding == "oaep":
            max_msg_len = n_bytes - 2 * hash_mod.digest_size - 2
            msg_len = int.from_bytes(random(2), "big") % (max_msg_len + 1)
            msg = random(msg_len)

            # Use an empty label ~25% of the time, otherwise random 1..=64 bytes.
            if random(1)[0] % 4 == 0:
                label = b""
            else:
                label_len = (
                    int.from_bytes(random(1), "big") % MAX_OAEP_LABEL_LEN + 1
                )
                label = random(label_len)

            cipher = PKCS1_OAEP.new(
                key, hashAlgo=hash_mod, label=label, randfunc=random
            )
            ct_bytes = cipher.encrypt(msg)

            test_vectors.append({
                "vendor": "random",
                "test_case_id": tc_id,
                "algorithm": "rsa",
                "operation": "encrypt",
                "padding": args.padding,
                "security_level": args.security_level,
                "hash_alg": args.hash_alg,
                "message": list(msg),
                "label": list(label),
                "n": n_bytes_list,
                "e": int(key.e),
                "d": d_bytes_list,
                "result": True,
            })
            tc_id += 1

            decrypt_ct = bytearray(ct_bytes)
            decrypt_result = True
            if random(1)[0] % 2 == 0:
                flip_random_bit(decrypt_ct, random)
                decrypt_result = False

            test_vectors.append({
                "vendor": "random",
                "test_case_id": tc_id,
                "algorithm": "rsa",
                "operation": "decrypt",
                "padding": args.padding,
                "security_level": args.security_level,
                "hash_alg": args.hash_alg,
                "message": list(msg),
                "label": list(label),
                "n": n_bytes_list,
                "e": int(key.e),
                "d": d_bytes_list,
                "ciphertext": list(decrypt_ct),
                "result": decrypt_result,
            })
            tc_id += 1
        else:
            raise ValueError(f"Unsupported RSA padding: {args.padding}")

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
        help="Number of random RSA keys to generate",
    )
    parser.add_argument(
        "--security_level",
        type=int,
        choices=[2048, 3072, 4096],
        required=True,
        help="RSA security level in bits",
    )
    parser.add_argument(
        "--padding",
        type=str,
        choices=["pkcs1_1.5", "pss", "oaep"],
        required=True,
        help="RSA padding mode",
    )
    parser.add_argument(
        "--hash_alg",
        type=str,
        choices=list(HASH_ALGS.keys()),
        required=True,
        help="Hash algorithm",
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
