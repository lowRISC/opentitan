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

    symbols_map = {}
    base_addr = None

    # Parse nm output (Format typically: 00000104 T function_name)
    for line in result.stdout.splitlines():
        match = re.match(r"^([0-9a-fA-F]+)\s+[A-Za-z]\s+(\w+)$", line.strip())
        if match:
            addr_hex, sym_name = match.groups()
            addr = int(addr_hex, 16)
            symbols_map[sym_name] = addr

            if sym_name == "_libotcrypto_start_":
                base_addr = addr

    if base_addr is None:
        sys.stderr.write(f"ERROR: _libotcrypto_start_ not found in {args.elf}\n")
        return 1

    objcopy_args = []

    # If config provided, strictly validate all symbols exist
    if keep_symbols:
        missing_symbols = keep_symbols - symbols_map.keys()
        if missing_symbols:
            sys.stderr.write(
                "ERROR: The following required symbols were missing from the ELF:\n"
            )
            for missing in missing_symbols:
                sys.stderr.write(f"  - {missing}\n")
            return 1

        target_symbols = keep_symbols
    else:
        target_symbols = symbols_map.keys()

    # Calculate relative offsets and generate objcopy flags
    for sym_name in target_symbols:
        if sym_name == "_libotcrypto_start_":
            continue

        offset = symbols_map[sym_name] - base_addr

        # Rename the old un-relaxed symbol to safely get it out of the way
        # Inject a brand new global symbol pointing precisely to the relaxed offset
        objcopy_args.append(f"--redefine-sym={sym_name}=__old_{sym_name}")
        objcopy_args.append(
            f"--add-symbol={sym_name}=.text.libotcrypto:{offset},global,function"
        )

    # Write the objcopy arguments to an options file
    with open(args.out, "w") as f:
        for arg in objcopy_args:
            f.write(f"{arg}\n")

    return 0


if __name__ == "__main__":
    sys.exit(main())
