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
        if group["curve"] != "curve25519":
            logging.info(
                f"Skipped test group: Unsupported curve type '{group['curve']}'"
            )
            continue

        for test in group["tests"]:
            logging.debug(f"Parsing tcId {test['tcId']}")

            if test["result"] != "valid":
                logging.info(
                    f"Skipped tcId {test['tcId']}: result is '{test['result']}'"
                )
                continue

            test_vec = {
                "vendor": "wycheproof",
                "test_case_id": test["tcId"],
                "algorithm": "x25519",
                "operation": "derive",
                "private_key": list(bytes.fromhex(test["private"])),
                "public_key": list(bytes.fromhex(test["public"])),
                "shared_secret": list(bytes.fromhex(test["shared"])),
                "result": "valid",
            }
            test_vectors.append(test_vec)

    return test_vectors


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--src",
        metavar="FILE",
        type=argparse.FileType("r"),
        help="Test vector input file to parse"
    )
    parser.add_argument(
        "--dst",
        metavar="FILE",
        type=argparse.FileType("w"),
        help="File to write parsed JSON test cases"
    )
    parser.add_argument(
        "--schema",
        type=str,
        help="Test vector schema file"
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


if __name__ == "__main__":
    sys.exit(main())
