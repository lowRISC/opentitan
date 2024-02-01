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
from cryptotest_util import str_to_byte_array

ALGORITHMS = {
    "SHA3": {
        224: "sha3-224",
        256: "sha3-256",
        384: "sha3-384",
        512: "sha3-512",
    },
    "SHAKE": {
        128: "shake-128",
        256: "shake-256",
    },
    "CSHAKE": {
        128: "cshake-128",
        256: "cshake-256",
    },
}


def parse_test_vectors(raw_data):
    test_vectors = []
    count = 1
    for test in raw_data:
        test_vec = {
            "vendor": "manual",
            "test_case_id": count,
            "algorithm": ALGORITHMS[test["operation"]][test["security_str"]],
            "message": str_to_byte_array(test["input_msg"]),
            "digest": str_to_byte_array(test["digest"]),
            "result": True,
        }
        if test["operation"] == "CSHAKE":
            test_vec["customization_string"] = str_to_byte_array(test["cust_str"])

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
    args = parser.parse_args()

    testvecs = parse_test_vectors(hjson.loads(args.src.read()))

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
