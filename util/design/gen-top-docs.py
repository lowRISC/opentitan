#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
r"""Generates top level documentation from an hjson configuration file."""

import argparse
import logging as log
from pathlib import Path

import hjson
from lib import common
from tabulate import tabulate


def to_markdown(text):
    """Adds prefix and sufix newlines to 'text'."""
    doc_text = f"""
{text}
"""
    return doc_text


def generate_mmap_table(top_level):
    """Generates top level memory map table."""
    header = ["Name", "Type", "Byte Address"]
    table = [header]
    colalign = ("left", ) * len(header)

    for module in top_level["module"]:
        for j, (name, base) in enumerate(module["base_addrs"].items()):

            base_address = f"{base} ({name})"
            if name == "null":
                base_address = f"{base} (regs)"

            if j == 0:
                row = [module["name"], module["type"], base_address]
            else:
                row = ["", "", base_address]

            table.append(row)

    return tabulate(table,
                    headers="firstrow",
                    tablefmt="pipe",
                    colalign=colalign)


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

    parser.add_argument("--topcfg",
                    "-t",
                    required=True,
                    help="Topgen generated config file `top_{name}.hjson`.")
    parser.add_argument(
        "--outdir",
        "-o",
        help="Target TOP documentation directory.")

    args = parser.parse_args()

    outdir = Path(args.outdir)

    doc_generators = [
        {
            "filename": "mmap.md",
            "generator": generate_mmap_table,
        },
        {
            "filename": "pinout.md",
            "generator": generate_pinout_table,
        },
    ]

    with open(args.topcfg, 'r') as infile:
        top_level = hjson.load(infile)
        top_outdir = outdir / top_level["name"]
        top_outdir.mkdir(parents=True, exist_ok=True)

        for doc in doc_generators:
            outfile = top_outdir / doc["filename"]
            table = doc["generator"](top_level)
            with open(outfile, 'w') as f:
                f.write(to_markdown(table))


if __name__ == "__main__":
    main()
