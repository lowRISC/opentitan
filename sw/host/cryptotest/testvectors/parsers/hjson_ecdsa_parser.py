#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import argparse
import json
import logging
import sys
import jsonschema
import hjson


def parse_test_vectors(raw_data, curve):
    test_vectors = []
    count = 1
    for test in raw_data:
        test_vec = {
            "vendor": "manual",
            "test_case_id": count,
            "algorithm": "ecdsa",
            "operation": "verify",
            "curve": curve,
            "hash_alg": "sha-256",
            "message": list(test["msg"].to_bytes(length=test["msg_len"], byteorder="big")),
            # Encode qx and qy as a string because downstream test vector
            # consumers may incorrectly handle large integers.
            "qx": hex(test["x"])[2:],
            "qy": hex(test["y"])[2:],
            "r": hex(test["r"])[2:],
            "s": hex(test["s"])[2:],
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
    parser.add_argument('--curve',
                        type=str,
                        help='Elliptic curve to use [p256, p384].')
    args = parser.parse_args()

    testvecs = parse_test_vectors(hjson.loads(args.src.read()), args.curve)

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
