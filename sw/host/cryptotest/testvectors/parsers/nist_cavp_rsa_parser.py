#!/usr/bin/env python3
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

"""Parser for converting NIST CAVP RSA test vectors to JSON.

"""

import argparse
import sys
import json
import jsonschema

from cryptotest_util import parse_rsp, str_to_byte_array

SUPPORTED_SECURITY_LEVELS = [
    2048,
    3072,
    4096,
]

HASH_NAME_MAPPING = {
    "SHA256": "sha-256",
    "SHA384": "sha-384",
    "SHA512": "sha-512",
}


def parse_testcases(args) -> None:
    # Depending on the operation, we have to notify the parser that certain
    # variables in the rsp file are not intended to be treated as a test case
    # on their own; instead, the values apply to all following test cases until
    # the variable is assigned another value.
    persists = []
    if args.operation == "sign":
        persists = ["n", "e", "d"]
    elif args.operation == "verify":
        persists = ["n", "p", "q"]
    else:
        raise ValueError(f"Unsupported RSA operation: {args.operation}")

    raw_testcases = parse_rsp(args.src, persists=persists)

    test_cases = list()
    # NIST splits the rsp files into sections with named after (curve, hash
    # algorithm) pairs
    count = 0
    for test_vec in raw_testcases:
        count += 1
        # Filter out unsupported configurations
        if int(test_vec["mod"]) not in SUPPORTED_SECURITY_LEVELS:
            continue
        if test_vec["SHAAlg"] not in HASH_NAME_MAPPING:
            continue
        test_case = {
            "vendor": "nist",
            "test_case_id": count,
            "algorithm": "rsa",
            "operation": args.operation,
            "padding": args.padding,
            "security_level": int(test_vec["mod"]),
            "hash_alg": HASH_NAME_MAPPING[test_vec["SHAAlg"]],
            "message": str_to_byte_array(test_vec["Msg"]),
            # Pad n and d with leading zero byte for compatibility
            # with signed hexadecimal notation.
            "n": [0] + str_to_byte_array(test_vec["n"]),
            "e": int(test_vec["e"], 16),
            "d": [0] + str_to_byte_array(test_vec["d"]) if "d" in test_vec else [],
            "signature": str_to_byte_array(test_vec["S"]),
        }
        if args.operation == "sign":
            # `Sign` tests always include the correct expected
            # signature.
            test_case["result"] = True
        elif args.operation == "verify":
            result_str = test_vec["Result"][:1]
            if result_str == "P":
                test_case["result"] = True
            elif result_str == "F":
                test_case["result"] = False
            else:
                raise ValueError(f"Unknown verification result value: {result_str}")

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
    parser.add_argument(
        "--operation",
        type = str,
        help = "RSA operation [sign, verify]"
    )
    parser.add_argument(
        "--padding",
        type = str,
        help = "RSA padding type [pkcs1_1.5, pss]"
    )
    args = parser.parse_args()
    parse_testcases(args)

    return 0


if __name__ == "__main__":
    sys.exit(main())
