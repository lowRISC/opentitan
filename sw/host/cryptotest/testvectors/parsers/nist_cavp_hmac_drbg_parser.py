#!/usr/bin/env python3
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

"""Parser for converting NIST CAVP HMAC DRBG test vectors to JSON."""

import argparse
import json
import sys
import jsonschema

from cryptotest_util import parse_rsp, str_to_byte_array


def parse_testcases(args) -> None:
    raw_testcases = parse_rsp(args.src)
    test_cases = list()

    test_count = 0
    # NIST splits the rsp files into sections based on tag length
    # (which implies which hash function should be used)
    for test_vec in raw_testcases:
        # Cryptolib supports SHA-256, SHA-384 and SHA-512 hashing
        # modes. Exclude tests for other configs.
        if test_vec["section_name"] in ("SHA-256", "SHA-384", "SHA-512"):
            test_count += 1
            test_case = {
                "vendor": "nist",
                "test_case_id": test_count,
                "algorithm": "drbg",
                "mode": test_vec["section_name"],
                "entropy": str_to_byte_array(test_vec["EntropyInput"]),
                "nonce": str_to_byte_array(test_vec["Nonce"]),
                "personalization_string": str_to_byte_array(test_vec["PersonalizationString"]),
                "reseed": args.reseed,
                "additional_input_1": str_to_byte_array(test_vec["AdditionalInput"][0]),
                "additional_input_2": str_to_byte_array(test_vec["AdditionalInput"][1]),
                "output": str_to_byte_array(test_vec["ReturnedBits"]),
                # All NIST DRBG vectors include the correct output in `ReturnedBits`.
                "result": True,
            }
        else:
            continue

        if args.reseed:
            test_case["reseed_entropy"] = str_to_byte_array(test_vec["EntropyInputReseed"])
            test_case["reseed_additional_input"] = str_to_byte_array(
                test_vec["AdditionalInputReseed"])

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
        description="Parsing utility for NIST CAVP DRBG test vectors.")

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
        type=str,
        help="Test vector schema file"
    )
    parser.add_argument(
        "--reseed",
        action="store_true",
        help="Whether the tests require reseeding"
    )
    args = parser.parse_args()
    parse_testcases(args)

    return 0


if __name__ == "__main__":
    sys.exit(main())
