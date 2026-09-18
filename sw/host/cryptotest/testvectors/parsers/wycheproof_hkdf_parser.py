#!/usr/bin/env python3
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import argparse
import json
import jsonschema
import logging
import sys

MAX_OKM_BYTES = 256


def parse_test_vectors(raw_data, hash_alg):
    test_groups = raw_data["testGroups"]
    test_vectors = list()
    for group in test_groups:
        for test in group["tests"]:
            if test["result"] == "valid" and test["size"] > MAX_OKM_BYTES:
                continue

            test_vec = {
                "vendor": "wycheproof",
                "test_case_id": test["tcId"],
                "algorithm": "hkdf",
                "hash_alg": hash_alg,
                "ikm": list(bytes.fromhex(test["ikm"])),
                "salt": list(bytes.fromhex(test["salt"])),
                "info": list(bytes.fromhex(test["info"])),
                "size": test["size"],
                "okm": list(bytes.fromhex(test["okm"])),
                "result": test["result"] == "valid",
            }
            test_vectors.append(test_vec)

    return test_vectors


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--src",
        metavar="FILE",
        type=argparse.FileType("r"),
        help="Read test vectors from this JSON file.",
    )
    parser.add_argument(
        "--dst",
        metavar="FILE",
        type=argparse.FileType("w"),
        help="Write output to this file.",
    )
    parser.add_argument(
        "--schema",
        type=str,
        help="Test vector schema file",
    )
    parser.add_argument(
        "--hash",
        type=str,
        help="Hash algorithm to use",
    )
    args = parser.parse_args()

    testvecs = parse_test_vectors(json.load(args.src), args.hash)
    args.src.close()

    with open(args.schema) as schema_file:
        schema = json.load(schema_file)
    jsonschema.validate(testvecs, schema)

    logging.info(f"Created {len(testvecs)} tests")
    json.dump(testvecs, args.dst)
    args.dst.close()

    return 0


if __name__ == "__main__":
    sys.exit(main())
