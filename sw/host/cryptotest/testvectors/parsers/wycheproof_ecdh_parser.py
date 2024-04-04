#!/usr/bin/env python3
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import argparse
import json
import jsonschema
import logging
import sys

from Crypto.PublicKey import ECC

# Mapping from the curve names used by Wycheproof to those used by cryptotest
EC_NAME_MAPPING = {
    "secp256r1": "p256",
    "secp384r1": "p384",
}


def parse_test_vectors(raw_data):
    test_groups = raw_data["testGroups"]
    test_vectors = list()
    for group in test_groups:
        # Parse tests within the group
        for test in group["tests"]:
            logging.debug(f"Parsing tcId {test['tcId']}")
            # A few tests are flagged as "InvalidASN" but the public key DER
            # string is nonetheless accepted by
            # Crypto.PublicKey.ECC.import_key(), so we manually exclude these
            # tests.
            if "InvalidAsn" in test["flags"]:
                logging.info(
                    f"Skipped tcId {test['tcId']}: Tagged as Invalid ASN."
                )
                continue
            test_vec = {
                "vendor": "wycheproof",
                "test_case_id": test['tcId'],
                "algorithm": "ecdh",
                "curve": EC_NAME_MAPPING[group["curve"]],
                "d": list(bytes.fromhex(test["private"])),
                "z": list(bytes.fromhex(test["shared"])),
            }

            # Parse ASN encoded public key
            if group["encoding"] == "asn":
                try:
                    public_key = ECC.import_key(bytes.fromhex(test["public"]))
                except ValueError as e:
                    logging.info(
                        f"Skipped tcId {test['tcId']}: ValueError when parsing DER sequence: {e}."
                    )
                    continue
                if public_key.curve != EC_NAME_MAPPING[group["curve"]]:
                    logging.info(
                        f"Skipped tcId {test['tcId']}: Curve in DER did not match test vector."
                    )
                    continue
                test_vec["qx"] = list(public_key.pointQ.x.to_bytes())
                test_vec["qy"] = list(public_key.pointQ.y.to_bytes())
            else:
                logging.info(
                    f"Skipped tcId {test['tcId']}: unsupported encoding '{group['encoding']}'."
                )
                continue

            # Parse the expected result
            if test["result"] == "valid":
                test_vec["result"] = True
            elif test["result"] == "invalid":
                test_vec["result"] = False
            elif test["result"] == "acceptable":
                # Wycheproof flags valid tests using compressed public keys as
                # "acceptable". We accept those tests, but reject others marked
                # "acceptable" to err on the side of caution.
                if "CompressedPoint" in test["flags"]:
                    test_vec["result"] = True
                else:
                    test_vec["result"] = False
            else:
                raise RuntimeError(f"Unexpected result type {test['result']}")

            test_vectors.append(test_vec)

    return test_vectors


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--src",
        metavar="FILE",
        type=argparse.FileType("r"),
        help="Test vector input file to parse"
    )
    parser.add_argument(
        "--dst",
        metavar="FILE",
        type=argparse.FileType("w"),
        help="File to write parsed JSON test cases"
    )
    parser.add_argument(
        "--schema",
        type = str,
        help = "Test vector schema file"
    )
    args = parser.parse_args()

    testvecs = parse_test_vectors(json.load(args.src))
    args.src.close()

    # Validate generated JSON
    with open(args.schema) as schema_file:
        schema = json.load(schema_file)
    jsonschema.validate(testvecs, schema)

    logging.info(f"Created {len(testvecs)} tests")
    json.dump(testvecs, args.dst)
    args.dst.close()

    return 0


if __name__ == "__main__":
    sys.exit(main())
