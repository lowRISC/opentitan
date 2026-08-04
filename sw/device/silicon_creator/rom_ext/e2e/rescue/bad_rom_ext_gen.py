# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""Reconstructs a binary file from an `xxd` hexdump, replacing `xxd -r`.

`xxd -r` isn't hermetic (it depends on the host having `xxd` on PATH), so
this reimplements just enough of it to reverse the hexdumps checked into
this directory (e.g. bad_rom_ext.txt): "OFFSET: hex-bytes  ascii" lines,
with a bare "*" line standing in for one or more omitted lines that repeat
the previous line's bytes.
"""
import sys


def main():
    src_path, dst_path = sys.argv[1], sys.argv[2]
    data = bytearray()
    prev_bytes = b""

    with open(src_path, encoding="ascii") as src:
        for line in src:
            line = line.rstrip("\n")
            if not line or line == "*":
                # A lone "*" just marks that one or more lines were elided
                # because they repeated the previous line; the next explicit
                # offset line tells us how far that repetition extends.
                continue

            offset_str, rest = line.split(":", 1)
            offset = int(offset_str, 16)
            hex_part = rest.strip().split("  ")[0]
            line_bytes = bytes.fromhex(hex_part.replace(" ", ""))

            if len(data) < offset and prev_bytes:
                # Fill the elided gap by repeating the previous line's bytes.
                gap = offset - len(data)
                repeats, remainder = divmod(gap, len(prev_bytes))
                assert remainder == 0, (
                    f"gap of {gap} bytes before offset {offset:#x} isn't a "
                    f"multiple of the previous line's {len(prev_bytes)} bytes"
                )
                data.extend(prev_bytes * repeats)

            if len(data) < offset:
                # No previous line to repeat (e.g. a leading gap): zero-fill.
                data.extend(b"\x00" * (offset - len(data)))

            data[offset:offset + len(line_bytes)] = line_bytes
            prev_bytes = line_bytes

    with open(dst_path, "wb") as dst:
        dst.write(data)


if __name__ == "__main__":
    main()
