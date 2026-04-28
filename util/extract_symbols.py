#!/usr/bin/env python3
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import argparse
import subprocess
import re
import sys


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Extract symbol offsets to generate objcopy arguments."
    )
    parser.add_argument("--nm", required=True, help="Path to the nm executable")
    parser.add_argument("--elf", required=True, help="Input ELF file")
    parser.add_argument("--config", help="File with functions to keep")
    parser.add_argument(
        "--out", required=True, help="Output arguments file for objcopy"
    )
    args = parser.parse_args()

    # Read config to know which functions to expose
    keep_symbols = set()
    if args.config:
        with open(args.config, "r") as f:
            keep_symbols = {line.strip() for line in f if line.strip()}

    # Run nm to get symbol addresses
    result = subprocess.run(
        [args.nm, "--defined-only", args.elf],
        capture_output=True,
        text=True,
        check=True,
    )

    # Parse nm output (Format typically: 00000104 T function_name)
    symbols = []
    for line in result.stdout.splitlines():
        match = re.match(r"^([0-9a-fA-F]+)\s+[A-Za-z]\s+(\w+)$", line)
        if match:
            addr_hex, sym_name = match.groups()

            # Filter by config if provided
            if not keep_symbols or sym_name in keep_symbols:
                offset = int(addr_hex, 16)
                # Format: <name>=<section>:<value>[,<flags>]
                symbols.append(
                    f"--add-symbol={sym_name}=.text.blob:{offset},global,function"
                )

    # Write the objcopy arguments to an options file
    with open(args.out, "w") as f:
        for sym in symbols:
            f.write(f"{sym}\n")

    return 0


if __name__ == "__main__":
    sys.exit(main())
