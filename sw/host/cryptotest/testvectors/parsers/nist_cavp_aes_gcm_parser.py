#!/usr/bin/env python3
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

"""Parser for converting NIST AES-GCM testvectors to JSON.

"""

import argparse
import sys
import json
import jsonschema

from cryptotest_util import parse_rsp, str_to_byte_array


def parse_testcases(args) -> None:
    raw_testcases = parse_rsp(args.src)
    test_cases = list()
    for test_case_id, test_vec in enumerate(raw_testcases):
        test_case = {
            "test_case_id": test_case_id,
            "vendor": "nist",
            "mode": "gcm",
            "operation": args.operation.lower(),
            "key_len": args.key_len,
            "key": str_to_byte_array(test_vec["Key"]),
            "aad": str_to_byte_array(test_vec["AAD"]),
            "iv": str_to_byte_array(test_vec["IV"]),
            "tag": str_to_byte_array(test_vec["Tag"]),
            "ciphertext": str_to_byte_array(test_vec["CT"]),
            "plaintext": str_to_byte_array(test_vec["PT"]) if "PT" in test_vec else [],
            "result": args.operation.lower() == "encrypt" or "PT" in test_vec,
        }
        # Currently, there are no FAIL cases in the GCM encryption test vectors.
        # However, for decryption test vectors, if a test vector lacks a Plaintext (PT) field,
        # the result of that particular test vector will be marked as FAIL.
        # Reference:
        # https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Algorithm-Validation-Program/documents/mac/gcmvs.pdf
        # Section 6.6.2

        # The cryptolib currently supports tag lengths of (4,8,12,16)
        # bytes and iv lengths of (12,16) bytes. Only select those
        # tests.
        tag_length_valid = False
        if len(test_case["tag"]) in (4, 8, 12, 16):
            tag_length_valid = True

        iv_length_valid = False
        if len(test_case["iv"]) in (12, 16):
            iv_length_valid = True

        aad_length_valid = False
        if len(test_case["aad"]) < 64:
            aad_length_valid = True

        ciphertext_length_valid = False
        if len(test_case["ciphertext"]) < 64:
            ciphertext_length_valid = True

        plaintext_length_valid = False
        if len(test_case["plaintext"]) < 64:
            plaintext_length_valid = True

        if (tag_length_valid & iv_length_valid & aad_length_valid &
                ciphertext_length_valid & plaintext_length_valid):
            test_cases.append(test_case)

    json_filename = args.dst
    with open(json_filename, "w") as file:
        json.dump(test_cases, file, indent=4)

    # Validate generated JSON
    with open(args.schema) as schema_file:
        schema = json.load(schema_file)
    jsonschema.validate(test_cases, schema)


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Parsing utility for AES-GCM testvectors.")

    parser.add_argument(
        "--src",
        help="Source file to import."
    )
    parser.add_argument(
        "--dst",
        help="Destination of the output file."
    )
    parser.add_argument(
        "--operation",
        choices = ["Encrypt", "Decrypt"],
        type = str,
        help="Type of operation."
    )
    parser.add_argument(
        "--key_len",
        choices = [128, 192, 256],
        type = int,
        help = "Length of key in bits."
    )
    parser.add_argument(
        "--schema",
        type = str,
        help = "Testvector schema file"
    )
    args = parser.parse_args()
    parse_testcases(args)

    return 0


if __name__ == "__main__":
    sys.exit(main())
