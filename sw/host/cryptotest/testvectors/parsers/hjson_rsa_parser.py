#!/usr/bin/env python3
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import argparse
import json
import logging
import sys
import jsonschema
import hjson
from cryptotest_util import int_to_byte_array


def parse_test_vectors(raw_data, security_level):
    test_vectors = []
    count = 1
    for test in raw_data:
        test_vec = {
            "vendor": "manual",
            "test_case_id": count,
            "algorithm": "rsa",
            "operation": "verify",
            "security_level": security_level,
            "padding": "pkcs1_1.5",
            "hash_alg": "sha-256",
            "message": int_to_byte_array(test["msg"]),
            "n": [0] + int_to_byte_array(test["n"]),
            "e": test["e"],
            "signature": int_to_byte_array(test["signature"]),
            "result": test["valid"],
        }
        test_vectors.append(test_vec)
        count += 1

    return test_vectors


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--src',
                        metavar='FILE',
                        type=argparse.FileType('r'),
                        help='Read test vectors from this JSON file.')
    parser.add_argument('--dst',
                        metavar='FILE',
                        type=argparse.FileType('w'),
                        help='Write output to this file.')
    parser.add_argument("--schema", type=str, help="Testvector schema file")
    parser.add_argument("--security_level", type=int, help="RSA security level [2048, 3072, 4096]")
    args = parser.parse_args()

    testvecs = parse_test_vectors(hjson.loads(args.src.read()), args.security_level)

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
