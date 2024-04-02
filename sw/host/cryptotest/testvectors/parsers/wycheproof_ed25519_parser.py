#!/usr/bin/env python3
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import argparse
import json
import jsonschema
import logging
import sys


def parse_test_vectors(raw_data):
    test_groups = raw_data["testGroups"]
    test_vectors = list()
    for group in test_groups:
        # Parse the key for the group
        key = group["publicKey"]
        if key["curve"] != "edwards25519":
            logging.info(f"Skipped test group: Unsupported curve type '{key['curve']}'")
            continue

        # Parse tests within the group
        for test in group["tests"]:
            logging.debug(f"Parsing tcId {test['tcId']}")
            test_vec = {
                "algorithm": "ed25519",
                "operation": "verify",
                "message": list(bytes.fromhex(test["msg"])),
                "public_key": list(bytes.fromhex(key["pk"])),
                "signature": list(bytes.fromhex(test["sig"])),
            }

            # Parse the expected result
            if test["result"] == "valid":
                test_vec["result"] = True
            elif test["result"] == "invalid":
                test_vec["result"] = False
            elif test["result"] == "acceptable":
                # Err on the side of caution and reject "acceptable" signatures
                test_vec["result"] = False
            else:
                raise RuntimeError(f"Unexpected result type {test['result']}")

            test_vectors.append(test_vec)

        return test_vectors


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument(
        '--src',
        metavar='FILE',
        type=argparse.FileType('r'),
        help='Read test vectors from this JSON file.'
    )
    parser.add_argument(
        '--dst',
        metavar='FILE',
        type=argparse.FileType('w'),
        help='Write output to this file.'
    )
    parser.add_argument(
        "--schema",
        type = str,
        help = "Testvector schema file"
    )
    args = parser.parse_args()

    testvecs = parse_test_vectors(json.load(args.src))
    args.src.close()

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
