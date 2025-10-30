#!/usr/bin/env python3
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
r"""Generates top level documentation from an hjson configuration file."""

import sys
import argparse
import logging as log

import hjson
from lib import common
from tabulate import tabulate


def to_markdown(text):
    """Adds prefix and suffix newlines to 'text'."""
    doc_text = f"""
{text}
"""
    return doc_text


def generate_pinout_table(top_level):
    """Generates top level pinout table."""
    header = ["ID", "Name", "Bank", "Type", "Connection Type", "Description"]
    table = [header]
    colalign = ("left", ) * len(header)

    for pad in top_level["pinout"]["pads"]:
        row = [pad["idx"], pad["name"], pad["bank"], pad["type"], pad["connection"], pad["desc"]]
        table.append(row)

    return tabulate(table,
                    headers="firstrow",
                    tablefmt="pipe",
                    colalign=colalign)


def main():
    log.basicConfig(level=log.WARNING,
                    format="%(levelname)s: %(message)s")

    parser = argparse.ArgumentParser(
        prog="gen-top-docs",
        description=common.wrapped_docstring(),
        formatter_class=argparse.RawDescriptionHelpFormatter)

    parser.add_argument(
        "--topcfg",
        "-t",
        required=True,
        help="Topgen generated config file `top_{name}.hjson`.",
    )
    parser.add_argument(
        "--generator",
        "-g",
        help="Select generator",
    )
    args = parser.parse_args()
    gen = args.generator

    doc_generators = {
        "pinout": generate_pinout_table,
    }
    with open(args.topcfg, 'r') as infile:
        top_level = hjson.load(infile)
        if gen not in doc_generators:
            sys.exit(f"Unknown generator {gen}")

        print(doc_generators[gen](top_level))


if __name__ == "__main__":
    main()
