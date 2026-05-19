#!/usr/bin/env python3
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import argparse
import json
import jsonschema
import logging
import sys

# Curve25519 field prime and Montgomery curve constant A.
_P = 2**255 - 19
_A = 486662


def _is_twist_point(public_key_hex):
    """Returns True if the u-coordinate is on the quadratic twist of Curve25519.

    A u-coordinate is on the twist when u^3 + A*u^2 + u is a non-residue mod p,
    i.e. its Legendre symbol equals -1.  OpenTitan's X25519 implementation
    rejects such points, so they must be treated as invalid test vectors.
    """
    u = int.from_bytes(bytes.fromhex(public_key_hex), 'little')
    u = u & ((1 << 255) - 1)  # clear bit 255, matching OTBN's bn.and mask step
    u = u % _P                 # reduce mod p, matching OTBN's bn.addm step
    rhs = (pow(u, 3, _P) + _A * pow(u, 2, _P) + u) % _P
    if rhs == 0:
        return False
    return pow(rhs, (_P - 1) // 2, _P) == _P - 1


def parse_test_vectors(raw_data):
    test_groups = raw_data["testGroups"]
    test_vectors = list()
    for group in test_groups:
        if group["curve"] != "curve25519":
            logging.info(
                f"Skipped test group: Unsupported curve type '{group['curve']}'"
            )
            continue

        for test in group["tests"]:
            logging.debug(f"Parsing tcId {test['tcId']}")

            if test["result"] != "valid":
                logging.info(
                    f"Skipped tcId {test['tcId']}: result is '{test['result']}'"
                )
                continue

            result = "valid"
            if _is_twist_point(test["public"]):
                logging.info(
                    f"tcId {test['tcId']}: overriding result to invalid "
                    f"(public key is on the quadratic twist, rejected by OpenTitan)"
                )
                result = "invalid"

            test_vec = {
                "vendor": "wycheproof",
                "test_case_id": test["tcId"],
                "algorithm": "x25519",
                "operation": "derive",
                "private_key": list(bytes.fromhex(test["private"])),
                "public_key": list(bytes.fromhex(test["public"])),
                "shared_secret": list(bytes.fromhex(test["shared"])),
                "result": result,
            }
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
        type=str,
        help="Test vector schema file"
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
