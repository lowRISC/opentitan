#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import argparse
import json
import logging
import sys

import jsonschema
from Crypto.Util.asn1 import DerSequence

# Mapping from the curve names used by Wycheproof to those used by cryptotest
EC_NAME_MAPPING = {
    "secp256r1": "p256",
    "secp384r1": "p384",
}


def _parse_der_signature(der_str):
    seq_der = DerSequence()
    seq_der.decode(
        bytes.fromhex(der_str),
        nr_elements=2,
        only_ints_expected=True,
        strict=True,
    )
    seq = seq_der[:]  # Convert the DerSequence object to a list

    # Some tests parse correctly as a DER sequence but produce extra values.
    # These tests should be reject for a bad DER-encoded signature
    if len(seq) != 2:
        raise ValueError(
            "Failed to parse DER-encoded signature into r and s values")
    return seq


def parse_test_vectors(raw_data):
    test_groups = raw_data["testGroups"]
    test_vectors = list()
    for group in test_groups:
        # Parse the key for the group
        key = group["key"]

        # Parse tests within the group
        for test in group["tests"]:
            logging.debug(f"Parsing tcId {test['tcId']}")
            test_vec = {
                "algorithm": "ecdsa",
                "operation": "verify",
                "curve": EC_NAME_MAPPING[key["curve"]],
                "hash_alg": group["sha"].lower(),
                "message": list(bytes.fromhex(test["msg"])),
                "qx": int(key["wx"], 16),
                "qy": int(key["wy"], 16),
            }

            # Parse r and s from DER-encoded signature
            # If the DER sequence fails to parse, then it may be malformed as
            # part of the test case. Cryptolib does not accept DER-encoded
            # input, so ignore this test case.
            try:
                signature_seq = _parse_der_signature(test["sig"])
            except ValueError:
                logging.info(
                    f"Skipped tcId {test['tcId']}: ValueError while parsing DER sequence."
                )
                continue
            except IndexError:
                logging.info(
                    f"Skipped tcId {test['tcId']}: IndexError while parsing DER sequence."
                )
                continue

            test_vec["r"], test_vec["s"] = signature_seq

            # Parse the expected result
            if test["result"] == "valid":
                test_vec["result"] = True
            elif test["result"] == "invalid":
                test_vec["result"] = False
            elif test["result"] == "acceptable":
                # Err on the side of caution and reject "acceptable" signatures
                test_vec["result"] = False
            else:
                raise RuntimeError(f"Unexpected result type {test['result']}")

            test_vectors.append(test_vec)

        return test_vectors


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--src',
                        metavar='FILE',
                        type=argparse.FileType('r'),
                        help='Read test vectors from this JSON file.')
    parser.add_argument('--dst',
                        metavar='FILE',
                        type=argparse.FileType('w'),
                        help='Write output to this file.')
    parser.add_argument("--schema", type=str, help="Testvector schema file")
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


if __name__ == '__main__':
    sys.exit(main())
