#!/usr/bin/env python3
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""Parser for converting NIST CAVP Digital Signatures test vectors to JSON.

"""
# TODO: Add more detailed docstring

import argparse
import json
import sys

import jsonschema
from cryptotest_util import parse_rsp, str_to_byte_array

SUPPORTED_HASHES = [
    "sha-256",
    "sha-384",
    "sha-512",
    "sha3-256",
    "sha3-384",
    "sha3-512",
]

# Mapping from the curve names used by NIST to those used by cryptotest
EC_NAME_MAPPING = {
    "P-256": "p256",
    #    TODO (#21067) uncomment when cryptolib supports P-384
    #    "P-384": "p384",
}


def parse_testcases(args) -> None:
    raw_testcases = parse_rsp(args.src)
    test_cases = list()

    test_count = 0
    # NIST splits the rsp files into sections with named after (curve, hash
    # algorithm) pairs
    for test_vec in raw_testcases:
        curve, hash_alg = test_vec["section_name"]
        hash_alg = hash_alg.lower()
        if hash_alg not in SUPPORTED_HASHES:
            continue
        if curve not in EC_NAME_MAPPING.keys():
            continue
        test_count += 1
        test_case = {
            "vendor": "nist",
            "test_case_id": test_count,
            "algorithm": "ecdsa",
            "operation": args.operation,
            "curve": EC_NAME_MAPPING[curve],
            "hash_alg": hash_alg,
            "message": str_to_byte_array(test_vec["Msg"]),
            "qx": test_vec["Qx"],
            "qy": test_vec["Qy"],
            "r": test_vec["R"],
            "s": test_vec["S"],
        }
        if args.operation == "sign":
            test_case["d"] = test_vec["d"]

        # Only `verify` test vectors include an explicit success/failure
        # value. `Sign` test vectors are always expected to succeed.
        if args.operation == "verify":
            # NIST test vectors express the expected result as a string
            # with a short description of the particular failure mode (if
            # applicable).  We can extract the pass/fail condition by
            # checking the first character of the result field.
            # Example passing vector: Result = P (0 )
            # Example failing vector: Result = F (3 - S Changed)
            result_str = test_vec["Result"][0]
            if result_str == "P":
                test_case["result"] = True
            elif result_str == "F":
                test_case["result"] = False
            else:
                raise ValueError(f"Unknown verification result value: {result_str}")
        else:
            test_case["result"] = True

        test_cases.append(test_case)

    json_filename = f"{args.dst}"
    with open(json_filename, "w") as file:
        json.dump(test_cases, file, indent=4)

    # Validate generated JSON
    with open(args.schema) as schema_file:
        schema = json.load(schema_file)
    jsonschema.validate(test_cases, schema)


def main() -> int:
    parser = argparse.ArgumentParser(
        description=
        "Parsing utility for NIST CAVP Digital Signatures test vectors.")

    parser.add_argument("--src", help="Source file to import.")
    parser.add_argument("--dst", help="Destination of the output file.")
    parser.add_argument("--schema", type=str, help="Test vector schema file")
    parser.add_argument(
        "--operation",
        type = str,
        help="ECDSA operation the test vectors in `src` are testing",
        choices=["sign", "verify"],
    )
    args = parser.parse_args()
    parse_testcases(args)

    return 0


if __name__ == "__main__":
    sys.exit(main())
