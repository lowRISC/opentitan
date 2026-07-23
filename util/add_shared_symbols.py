#!/usr/bin/env python3
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import argparse
import re
import subprocess
import sys


def get_symbol_table(elf, objdump_path):
    """Runs objdump -t on the ELF and parses the output.

    Returns a dict mapping symbol name to its address (int).
    """
    try:
        objdump_res = subprocess.run(
            [objdump_path, "-t", elf],
            check=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            universal_newlines=True,
        )
    except subprocess.CalledProcessError as e:
        print(f"Error running objdump: {e.stderr}", file=sys.stderr)
        sys.exit(1)

    symbols = {}
    # Matches: <address> <flags> <section> <size> <name>
    # Address can be 8 or 16 hex chars, or spaces (for undefined symbols)
    # Flags is 7 chars. Section is non-whitespace. Size is hex. Name is non-whitespace.
    pattern = re.compile(
        r"^([0-9a-fA-F]{8,16}| {8,16}) (.{7}) (\S+)\s+([0-9a-fA-F]{8,16})\s+(\S+)"
    )
    for line in objdump_res.stdout.splitlines():
        m = pattern.match(line)
        if not m:
            continue
        addr_str, flags, section, size_str, name = m.groups()

        if section == "*UND*":
            continue

        try:
            addr = int(addr_str, 16) if addr_str.strip() else 0
            symbols[name] = addr
        except ValueError:
            continue
    return symbols


def main():
    parser = argparse.ArgumentParser(
        description="Convert binary to object file and add shared symbols."
    )
    parser.add_argument(
        "-b", "--bin", required=True, help="Input binary file."
    )
    parser.add_argument("-e", "--elf", help="Input ELF file.")
    parser.add_argument("-o", "--output", required=True, help="Output .o file.")
    parser.add_argument(
        "-s",
        "--symbol",
        action="append",
        dest="symbols",
        help="Symbol name to export. Can be specified multiple times.",
    )
    parser.add_argument(
        "--output-section",
        default=".rodata",
        help="Section name for the binary blob.",
    )
    parser.add_argument(
        "--abs", action="store_true", help="Export symbols as absolute symbols."
    )
    parser.add_argument(
        "--prefix", default="", help="Prefix to add to exported symbols."
    )
    parser.add_argument(
        "--objcopy", default="llvm-objcopy", help="Path to objcopy tool."
    )
    parser.add_argument(
        "--objdump", default="llvm-objdump", help="Path to objdump tool."
    )

    args = parser.parse_args()

    symbols_to_export = args.symbols if args.symbols else []

    objcopy_args = [
        args.objcopy,
        "-I",
        "binary",
        "-O",
        "elf32-littleriscv",
        "--rename-section",
        f".data={args.output_section}",
    ]

    if symbols_to_export:
        if not args.elf:
            print(
                "Error: --elf is required when exporting symbols.",
                file=sys.stderr,
            )
            sys.exit(1)

        symbol_table = get_symbol_table(args.elf, args.objdump)

        # Match symbols
        matched_symbols = {}
        missing_symbols = []
        for sym_name in symbols_to_export:
            if sym_name in symbol_table:
                matched_symbols[sym_name] = symbol_table[sym_name]
            else:
                missing_symbols.append(sym_name)

        if missing_symbols:
            for sym_name in missing_symbols:
                print(
                    f"Error: symbol '{sym_name}' not found in ELF.",
                    file=sys.stderr,
                )
            sys.exit(1)

        for sym_name, addr in matched_symbols.items():
            export_name = f"{args.prefix}{sym_name}"
            if args.abs:
                # Absolute symbol
                objcopy_args.append(f"--add-symbol={export_name}=0x{addr:x},global")
            else:
                # Relative symbol (offset is same as address if base is assumed to be 0)
                objcopy_args.append(
                    f"--add-symbol={export_name}={args.output_section}:0x{addr:x},global"
                )

    objcopy_args.extend([args.bin, args.output])

    try:
        subprocess.run(
            objcopy_args,
            check=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            universal_newlines=True,
        )
    except subprocess.CalledProcessError as e:
        print(f"Error running objcopy: {e.stderr}", file=sys.stderr)
        sys.exit(1)


if __name__ == "__main__":
    main()
