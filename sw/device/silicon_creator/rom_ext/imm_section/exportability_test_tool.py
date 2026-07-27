#!/usr/bin/env python3
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import argparse
import subprocess
import sys
import re


def main():
    parser = argparse.ArgumentParser(description="Verify imm_section exportability.")
    parser.add_argument("object", help="The object file to check.")
    parser.add_argument("--objdump", default="llvm-objdump", help="Path to objdump tool.")
    parser.add_argument(
        "--expect-fail",
        action="store_true",
        help="Expect the verification to fail.",
    )
    args = parser.parse_args()

    # Run objdump -h to get section headers
    try:
        res = subprocess.run(
            [args.objdump, "-h", args.object],
            check=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            universal_newlines=True,
        )
    except subprocess.CalledProcessError as e:
        print(f"Error running objdump: {e.stderr}", file=sys.stderr)
        sys.exit(1)

    print("Objdump output:")
    print(res.stdout)

    # Run objdump -t to get symbol table
    try:
        res_t = subprocess.run(
            [args.objdump, "-t", args.object],
            check=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            universal_newlines=True,
        )
        print("Symbol table:")
        print(res_t.stdout)
    except subprocess.CalledProcessError as e:
        print(f"Error running objdump -t: {e.stderr}", file=sys.stderr)

    # Parse sections and check sizes for .data and .bss
    # Lines look like:
    #  Idx Name          Size      VMA       LMA       File off  Algn
    #    0 .text         000000a4  ...
    # We look for .data and .bss and check if size is non-zero.
    # Note that sections might not exist, which is fine (size is 0).

    # Matches: index name size ...
    # Section name is group 2, size is group 3.
    pattern = re.compile(r"^\s*(\d+)\s+(\.\S+)\s+([0-9a-fA-F]+)")
    section_pattern = re.compile(r"^\.(data|bss|sbss|sdata)(\..*)?$")

    failed = False
    for line in res.stdout.splitlines():
        m = pattern.match(line)
        if not m:
            continue
        idx, name, size_hex = m.groups()
        if section_pattern.match(name):
            size = int(size_hex, 16)
            if size > 0:
                print(
                    f"ERROR: Section {name} has non-zero size: {size_hex} "
                    f"({size} bytes)",
                    file=sys.stderr,
                )
                failed = True

    if failed:
        if args.expect_fail:
            print("PASS: Verification failed as expected.")
            sys.exit(0)
        else:
            sys.exit(1)
    else:
        if args.expect_fail:
            print("FAIL: Expected verification to fail, but it passed!", file=sys.stderr)
            sys.exit(1)
        else:
            print("PASS: .data and .bss are empty or absent.")
            sys.exit(0)


if __name__ == "__main__":
    main()
