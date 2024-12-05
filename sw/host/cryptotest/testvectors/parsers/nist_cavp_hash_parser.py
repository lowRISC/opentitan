#!/usr/bin/env python3
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

"""Parser for converting NIST CAVP Hash Function test vectors to JSON.

"""

import argparse
import sys
import json
import jsonschema

from cryptotest_util import parse_rsp, str_to_byte_array

# Map hash function names as formatted in the test vectors to their
# JSON schema names
HASH_FUNCTION_NAME_MAPPING = {
    "SHA256": "sha-256",
    "SHA384": "sha-384",
    "SHA512": "sha-512",
    "SHA3_224": "sha3-224",
    "SHA3_256": "sha3-256",
    "SHA3_384": "sha3-384",
    "SHA3_512": "sha3-512",
    "SHAKE128": "shake-128",
    "SHAKE256": "shake-256",
}


def parse_testcases(args) -> None:
    raw_testcases = parse_rsp(args.src)
    test_cases = list()
    algorithm = HASH_FUNCTION_NAME_MAPPING[args.algorithm]
    # The test vectors for the SHA functions use "MD" as the key for
    # the message digest. SHAKE functions use "Output".
    if algorithm.startswith("shake"):
        digest_key = "Output"
    else:
        digest_key = "MD"
    count = 1
    for test_vec in raw_testcases:
        # The test vector includes a single placeholder zero byte if its
        # intended message length is 0, so we need to ignore that byte.
        if "Len" in test_vec and int(test_vec["Len"]) == 0:
            message = []
        else:
            message = str_to_byte_array(test_vec["Msg"])
        if "COUNT" in test_vec:
            test_case_id = int(test_vec["COUNT"])
        else:
            test_case_id = count
        test_case = {
            "vendor": "nist",
            "test_case_id": test_case_id,
            "algorithm": algorithm,
            "message": message,
            "digest": str_to_byte_array(test_vec[digest_key]),
            # All NIST hash test vectors are expected to have the
            # right message digest
            "result": True,
        }

        test_cases.append(test_case)
        count += 1

    json_filename = f"{args.dst}"
    with open(json_filename, "w") as file:
        json.dump(test_cases, file, indent=4)

    # Validate generated JSON
    with open(args.schema) as schema_file:
        schema = json.load(schema_file)
    jsonschema.validate(test_cases, schema)


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Parsing utility for NIST CAVP Hash Function test vectors.")

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
        "--algorithm",
        type = str,
        help = "Hash algorithm the test vectors are testing"
    )
    args = parser.parse_args()
    parse_testcases(args)

    return 0


if __name__ == "__main__":
    sys.exit(main())
