#!/usr/bin/env python3
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

"""Parser for converting NIST CAVP Digital Signatures test vectors to JSON.

"""

import argparse
import sys
import json
import jsonschema

from cryptotest_util import parse_rsp

# NIST vectors allow differently-sized MACs for each hash function
# (https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Algorithm-Validation-Program/documents/mac/HMACVS.pdf).
# However, the test vectors only include the longest length for each
# hash (i.e. the entire hash is the MAC).
LENGTH_TO_HASH = {
    "32": "sha-256",
    "48": "sha-384",
    "64": "sha-512",
}

HASH_TO_LENGTH = {
    "sha256": "32",
    "sha384": "48",
    "sha512": "64",
}


def parse_testcases(args) -> None:
    raw_testcases = parse_rsp(args.src)
    test_cases = list()
    length = HASH_TO_LENGTH[args.hash]
    for test_vec in raw_testcases:
        # Tag length indicates which hash function should be used
        mac_len = test_vec["L"]
        if length != mac_len or mac_len not in LENGTH_TO_HASH:
            # Some hash functions in the test vector (e.g. SHA-1) are not
            # supported by OpenTitan.
            continue
        test_case = {
            "vendor": "nist",
            "test_case_id": int(test_vec["Count"]),
            "algorithm": "hmac",
            "hash_alg": LENGTH_TO_HASH[mac_len],
            "key": list(bytes.fromhex(test_vec["Key"])),
            "message": list(bytes.fromhex(test_vec["Msg"])),
            "tag": list(bytes.fromhex(test_vec["Mac"])),
            # All NIST HMAC vectors are expected to pass
            "result": True,
        }
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
        "--hash",
        help="Which hash algorithm to output test vectors for",
        choices=["sha256", "sha384", "sha512"]
    )
    args = parser.parse_args()
    parse_testcases(args)

    return 0


if __name__ == "__main__":
    sys.exit(main())
