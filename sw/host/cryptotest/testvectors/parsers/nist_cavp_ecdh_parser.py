#!/usr/bin/env python3
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

"""Parser for converting NIST CAVP ECDH test vectors to JSON.

"""

import argparse
import sys
import json
import jsonschema

from cryptotest_util import parse_rsp


# Mapping from the curve names used by NIST to those used by cryptotest
EC_NAME_MAPPING = {
    "P-256": "p256",
    # TODO uncomment when ECDH supports P-384
    # "P-384": "p384",
}


def parse_testcases(args) -> None:
    raw_testcases = parse_rsp(args.src)
    test_cases = list()

    # NIST splits the rsp files into sections with named after the ECC curve.
    for test_vec in raw_testcases:
        if test_vec["section_name"] not in EC_NAME_MAPPING.keys():
            continue
        test_case = {
            "vendor": "nist",
            "test_case_id": int(test_vec["COUNT"]),
            "algorithm": "ecdh",
            "curve": EC_NAME_MAPPING[test_vec["section_name"]],
            # 'CAVS' here stands for the NIST Cryptographic Algorithm
            # Validation System. In other words, the test harness is
            # serving as the other peer in the shared key derivation, and
            # the IUT needs the other peer's public key.
            "qx": list(bytes.fromhex(test_vec["QCAVSx"])),
            "qy": list(bytes.fromhex(test_vec["QCAVSy"])),
            "d": list(bytes.fromhex(test_vec["dIUT"])),
            "z": list(bytes.fromhex(test_vec["ZIUT"])),
            # All NIST test vectors are expected to produce the given
            # shared secret (z).
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
    args = parser.parse_args()
    parse_testcases(args)

    return 0


if __name__ == "__main__":
    sys.exit(main())
