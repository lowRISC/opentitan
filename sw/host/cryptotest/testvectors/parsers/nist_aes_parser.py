#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

"""Parser for converting NIST AES testvectors to JSON.

NIST AES testvectors are given as rsp files. Each rsp file contains
newline-delimited test vectors grouped into two sections: ENCRYPT and DECRYPT.
"""

import argparse
import sys
import json
import jsonschema

from cryptotest_util import parse_rsp, str_to_byte_array


def parse_testcases(args) -> None:
    raw_testcases = parse_rsp(args.src)
    testcases = list()
    for operation in raw_testcases.keys():
        # RSP file is expected to contain two groups: ENCRYPT and DECRYPT
        if operation not in ["ENCRYPT", "DECRYPT"]:
            raise ValueError(f"Unexpected group name {operation} in RSP file")
        for test_vec in raw_testcases[operation]:
            testcase = {
                "algorithm": "aes",
                "operation": operation.lower(),
                "key_len": args.key_len,
                "mode": args.mode,
                "padding": "null",
                "key": str_to_byte_array(test_vec["KEY"]),
            }

            # ECB does not have an IV
            if args.mode != "ecb":
                testcase["iv"] = str_to_byte_array(test_vec["IV"])

            # CFB1 is a special case where the block size is only 1 bit
            if args.mode == "cfb1":
                testcase["ciphertext"] = [int(test_vec["CIPHERTEXT"])]
                testcase["plaintext"] = [int(test_vec["PLAINTEXT"])]
            else:
                testcase["ciphertext"] = str_to_byte_array(test_vec["CIPHERTEXT"])
                testcase["plaintext"] = str_to_byte_array(test_vec["PLAINTEXT"])

            testcases.append(testcase)

    json_filename = f"{args.dst}.json"
    with open(json_filename, "w") as file:
        json.dump(testcases, file, indent=4)

    # Validate generated JSON
    with open(args.schema) as schema_file:
        schema = json.load(schema_file)
    jsonschema.validate(testcases, schema)


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Parsing utility for AES testvectors.")
    parser.add_argument(
        "src",
        help="Source file to import."
    )
    parser.add_argument(
        "dst",
        help="Destination of the output file."
    )
    parser.add_argument(
        "mode",
        choices = ["ecb", "ofb", "cbc", "cfb1", "cfb8", "cfb128"],
        help = "Block cipher mode of operation."
    )
    parser.add_argument(
        "key_len",
        choices = [128, 192, 256],
        type = int,
        help = "Length of key in bits."
    )
    parser.add_argument(
        "schema",
        type = str,
        help = "Testvector schema file"
    )
    args = parser.parse_args()
    parse_testcases(args)

    return 0


if __name__ == "__main__":
    sys.exit(main())
