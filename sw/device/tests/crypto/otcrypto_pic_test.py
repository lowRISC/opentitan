# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import argparse
import bisect
import subprocess
import sys
import tempfile
from typing import List, Tuple
from python.runfiles import Runfiles


def run_cmd(cmd: List[str]) -> str:
    """Runs a command and returns its stdout."""
    result = subprocess.run(cmd, check=True, capture_output=True, text=True)
    return result.stdout


def get_lowest_vma(objdump: str, elf: str) -> int:
    """Finds the base load address by looking at loadable sections."""
    # Try program headers first
    out = run_cmd([objdump, "-p", elf])
    for line in out.splitlines():
        if "LOAD" in line and "vaddr" in line:
            parts = line.split()
            vaddr_idx = parts.index("vaddr") + 1
            return int(parts[vaddr_idx], 16)

    # Fallback to section headers
    out = run_cmd([objdump, "-h", elf])
    vmas = []
    for line in out.splitlines():
        parts = line.split()
        if len(parts) >= 6 and parts[0].isdigit():
            vmas.append(int(parts[3], 16))

    return min(vmas) if vmas else 0


def get_symbols(nm: str, elf: str) -> Tuple[List[int], List[Tuple[int, int, str]]]:
    """Returns sorted addresses and a corresponding list of (addr, size, name)."""
    out = run_cmd([nm, "-S", "--numeric-sort", elf])
    symbols = []
    addresses = []

    for line in out.splitlines():
        parts = line.split()
        addr = int(parts[0], 16)

        if len(parts) >= 4:
            size = int(parts[1], 16)
            name = parts[3]
        elif len(parts) == 3:
            size = 0
            name = parts[2]
        else:
            continue

        addresses.append(addr)
        symbols.append((addr, size, name))

    return addresses, symbols


def find_symbol(
    addresses: List[int], symbols: List[Tuple[int, int, str]], target_addr: int
) -> str:
    """Find the symbol containing the target address."""
    # Find the insertion point
    idx = bisect.bisect_right(addresses, target_addr) - 1
    if idx < 0:
        return "<unknown>"

    addr, size, name = symbols[idx]

    return name


def main():
    r = Runfiles.Create()
    parser = argparse.ArgumentParser()
    parser.add_argument("--elf-base", required=True)
    parser.add_argument("--elf-offset", required=True)
    parser.add_argument("--objcopy", required=True)
    parser.add_argument("--objdump", required=True)
    parser.add_argument("--nm", required=True)
    parser.add_argument("--dis-base", required=True)
    parser.add_argument("--dis-offset", required=True)
    args = parser.parse_args()

    vma_base = get_lowest_vma(args.objdump, args.elf_base)

    # Extract full binary images
    with tempfile.NamedTemporaryFile() as bin_base, tempfile.NamedTemporaryFile() as bin_offset:
        subprocess.run(
            [args.objcopy, "-O", "binary", args.elf_base, bin_base.name], check=True
        )
        subprocess.run(
            [args.objcopy, "-O", "binary", args.elf_offset, bin_offset.name], check=True
        )

        b1 = open(bin_base.name, "rb").read()
        b2 = open(bin_offset.name, "rb").read()

    if len(b1) != len(b2):
        sys.exit(
            f"\nERROR: Binary sizes differ. (Base: {len(b1)}B vs Shifted: {len(b2)}B)"
        )

    # Find all differing byte offsets
    diff_offsets = [i for i, (byte1, byte2) in enumerate(zip(b1, b2)) if byte1 != byte2]

    if not diff_offsets:
        print("\nPASS: Blob is position-independent")
        sys.exit(0)

    # Trace differences to symbols using binary search
    addresses, symbols = get_symbols(args.nm, args.elf_base)
    bad_symbols = set()

    for offset in diff_offsets:
        target_addr = vma_base + offset
        bad_symbols.add(find_symbol(addresses, symbols, target_addr))

    print("\n ERROR: Absolute addresses detected")
    print("references inside the following symbols:\n")
    for sym in sorted(bad_symbols):
        print(f"  - {sym}")

    print("\nFor manual inspection, compare the corresponding disassembly files:")

    base_dis_abs = r.Rlocation('lowrisc_opentitan/' + args.dis_base)
    shifted_dis_abs = r.Rlocation('lowrisc_opentitan/' + args.dis_offset)

    print(f"  Base DIS:    {base_dis_abs}")
    print(f"  Shifted DIS: {shifted_dis_abs}")

    sys.exit(1)


if __name__ == "__main__":
    main()
