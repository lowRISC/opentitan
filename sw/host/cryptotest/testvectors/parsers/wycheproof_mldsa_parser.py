#!/usr/bin/env python3
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import argparse
import json
import logging
import sys

try:
    import jsonschema
except ImportError:
    jsonschema = None


def parse_test_vectors(raw_data):
    test_groups = raw_data["testGroups"]
    test_vectors = list()
    for group in test_groups:
        param = group.get("parameterSet")
        if param and param != "ML-DSA-87":
            logging.info(f"Skipped test group: Unsupported parameterSet '{param}'")
            continue

        group_type = group.get("type", "")
        for test in group["tests"]:
            logging.debug(f"Parsing tcId {test['tcId']}")

            if "msg" not in test:
                continue

            is_valid = test.get("result") == "valid"
            ctx_hex = test.get("ctx", group.get("ctx", ""))
            ctx_bytes = list(bytes.fromhex(ctx_hex)) if ctx_hex else []

            if "Sign" in group_type:
                test_vec = {
                    "vendor": "wycheproof",
                    "test_case_id": test["tcId"],
                    "algorithm": "ml-dsa",
                    "operation": "sign",
                    "parameter_set": "ml-dsa-87",
                    "private_seed": list(bytes.fromhex(group["privateSeed"]))
                    if group.get("privateSeed")
                    else [],
                    "public_key": list(bytes.fromhex(group["publicKey"]))
                    if group.get("publicKey")
                    else [],
                    "message": list(bytes.fromhex(test["msg"])) if test.get("msg") else [],
                    "context": ctx_bytes,
                    "rnd": list(bytes.fromhex(test["rnd"])) if test.get("rnd") else [],
                    "signature": list(bytes.fromhex(test["sig"])) if test.get("sig") else [],
                    "result": is_valid,
                }
            else:
                test_vec = {
                    "vendor": "wycheproof",
                    "test_case_id": test["tcId"],
                    "algorithm": "ml-dsa",
                    "operation": "verify",
                    "parameter_set": "ml-dsa-87",
                    "public_key": list(bytes.fromhex(group["publicKey"]))
                    if group.get("publicKey")
                    else [],
                    "message": list(bytes.fromhex(test["msg"])) if test.get("msg") else [],
                    "context": ctx_bytes,
                    "signature": list(bytes.fromhex(test["sig"])) if test.get("sig") else [],
                    "result": is_valid,
                }
            test_vectors.append(test_vec)

    return test_vectors


def main():
    parser = argparse.ArgumentParser(
        description="Convert Wycheproof ML-DSA test vectors to JSON format."
    )
    parser.add_argument(
        "--src",
        metavar="FILE",
        type=argparse.FileType("r"),
        default=sys.stdin,
        help="Input Wycheproof JSON testvector file",
    )
    parser.add_argument(
        "--dst",
        metavar="FILE",
        type=argparse.FileType("w"),
        default=sys.stdout,
        help="Output JSON testvector file",
    )
    parser.add_argument(
        "--schema",
        metavar="FILE",
        type=argparse.FileType("r"),
        help="JSON schema file for validation",
    )
    args = parser.parse_args()

    raw_data = json.load(args.src)
    test_vectors = parse_test_vectors(raw_data)

    if args.schema and jsonschema is not None:
        schema = json.load(args.schema)
        jsonschema.validate(instance=test_vectors, schema=schema)

    json.dump(test_vectors, args.dst, indent=2)


if __name__ == "__main__":
    main()
