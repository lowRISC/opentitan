#!/usr/bin/env python3
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

"""Parser for converting SPHINCS+ RSP test vectors to JSON.

"""

import argparse
import sys
import json
import jsonschema

from cryptotest_util import parse_rsp, str_to_byte_array


def parse_testcases(args) -> None:
    raw_testcases = parse_rsp(args.src)
    test_cases = list()

    # The SPHINCS+ RSP files do not use named sections.
    for test_vec in raw_testcases:
        test_cases.append({
            "vendor": "sphincs+",
            "test_case_id": int(test_vec["count"]),
            "algorithm": "sphincs+",
            "operation": "verify",
            "hash_alg": args.hash_alg,
            "public": str_to_byte_array(test_vec["pk"]),
            "message": str_to_byte_array(test_vec["msg"]),
            # Parse the signature from `sm` by removing the message from the end.
            "signature": str_to_byte_array(test_vec['sm'][:-len(test_vec['msg'])]),
            "result": True,
        })

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
        "--hash_alg",
        type= str,
        help = "Hash algorithm to use"
    )
    args = parser.parse_args()
    parse_testcases(args)

    return 0


if __name__ == "__main__":
    sys.exit(main())
