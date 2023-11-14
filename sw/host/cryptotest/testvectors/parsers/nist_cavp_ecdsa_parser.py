#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

"""Parser for converting NIST CAVP Digital Signatures test vectors to JSON.

"""
# TODO: Add more detailed docstring

import argparse
import sys
import json
import jsonschema

from cryptotest_util import parse_rsp, str_to_byte_array


SUPPORTED_NIST_CURVES = ["P-256", "P-384"]


def parse_testcases(args) -> None:
    raw_testcases = parse_rsp(args.src)
    test_cases = list()

    # NIST splits the rsp files into sections with named after (curve, hash
    # algorithm) pairs
    for section_name in raw_testcases.keys():
        curve, hash_alg = section_name.split(",")
        if curve not in SUPPORTED_NIST_CURVES:
            continue
        for test_vec in raw_testcases[section_name]:
            test_case = {
                "algorithm": "ecdsa",
                "operation": "verify",
                "curve": curve.lower(),
                "hash_alg": hash_alg.lower(),
                "message": str_to_byte_array(test_vec["Msg"]),
                "qx": int(test_vec["Qx"], 16),
                "qy": int(test_vec["Qy"], 16),
                "r": int(test_vec["R"], 16),
                "s": int(test_vec["S"], 16),
            }

            # NIST test vectors express the expected result as a string with a
            # short description of the particular failure mode (if applicable).
            # We can extract the pass/fail condition by checking the first
            # character of the result field.
            # Example passing vector: Result = P (0 )
            # Example failing vector: Result = F (3 - S Changed)
            result_str = test_vec["Result"][0]
            if result_str == "P":
                test_case["result"] = True
            elif result_str == "F":
                test_case["result"] = False
            else:
                raise ValueError(f"Unknown verification result value: {result_str}")

            test_cases.append(test_case)

    json_filename = f"{args.dst}.json"
    with open(json_filename, "w") as file:
        json.dump(test_cases, file, indent=4)

    # Validate generated JSON
    with open(args.schema) as schema_file:
        schema = json.load(schema_file)
    jsonschema.validate(test_cases, schema)


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Parsing utility for NIST CAVP Digital Signatures test vectors.")

    parser.add_argument(
        "--src",
        help="Source file to import."
    )
    parser.add_argument(
        "--dst",
        help="Destination of the output file."
    )
    parser.add_argument(
        "--schema",
        type = str,
        help = "Test vector schema file"
    )
    args = parser.parse_args()
    parse_testcases(args)

    return 0


if __name__ == "__main__":
    sys.exit(main())
