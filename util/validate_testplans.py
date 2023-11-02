#!/usr/bin/env python3
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

"""
This script validates the various opentitan testplan.hjson files.
Usage:
    ./util/validate_testplans.py --schema hw/lint/sival_testplan_schema.hjson \
                                 --dir hw/top_earlgrey/data/
    ./util/validate_testplans.py --schema hw/lint/sival_testplan_schema.hjson \
                                 --dir hw/top_earlgrey/data/ip/
"""

import argparse
import glob
import logging
import sys
import pathlib
import hjson
import jsonschema


def main(args: argparse.Namespace) -> int:
    files = [f for f in glob.glob(f"{args.dir}/*.hjson")]

    assert args.schema
    return SchemaValidator(args.schema).check(files)


class SchemaValidator:
    def __init__(self, schema_file: str):
        self.schema = hjson.load(open(schema_file, "r", encoding="utf-8"))

    def check(self, files: str) -> int:
        res: int = 0
        for f in files:
            try:
                testplan = hjson.load(open(f, "r", encoding="utf-8"))
                jsonschema.validate(testplan, schema=self.schema)

            except jsonschema.ValidationError as e:
                logging.info("Validation failed on file %s: %s", f, e)
                res = -1
            except hjson.scanner.HjsonDecodeError as e:
                logging.info("Failed to decode file %s: %s", f, e)
                res = -1
                break

        if res == 0:
            logging.info("No errors found!")
        else:
            logging.info("Errors found - run validation locally with %s", " ".join(sys.argv))
        return res


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--logging",
        default="info",
        choices=["debug", "info", "warning", "error", "critical"],
        help="Logging level",
    )
    parser.add_argument(
        "--dir",
        required=True,
        help="A directory containing testplan.hjson files.",
    )
    parser.add_argument(
        "--schema",
        required=True,
        type=pathlib.Path,
        help="A hjson file with the validation rules to be used.",
    )

    args = parser.parse_args()
    logging.basicConfig(level=args.logging.upper())
    sys.exit(main(args))
