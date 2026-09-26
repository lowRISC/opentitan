#!/usr/bin/env python3
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""Sanitize a file by removing any invalid UTF-8 byte sequences, and any
valid UTF-8 byte sequences that XML 1.0 does not permit.
"""

import sys
from pathlib import Path


def sanitize_xml(file_path: Path) -> None:
    """
    Sanitize the contents of a file, replacing any invalid UTF-8 characters with the
    Replacement Character, and removing any characters forbidden by the XML 1.0 spec.

    Args:
        file_path: The file to sanitize, which will be overwritten.
    """
    # Replace non-UTF-8 characters with backslashed escape sequences
    text = file_path.read_text(encoding="utf-8", errors="backslashreplace")

    # Remove any characters forbidden by XML 1.0
    # https://www.w3.org/TR/xml/#charsets
    text = "".join(
        char for char in text
        # Char ::= "#x9 | #xA | #xD" | ...
        if char in "\t\n\r" or
        # Char ::= ... | [#x20-#xD7FF] | [#xE000-#xFFFD] | [#x10000-#x10FFFF]
        # i.e. "Any Unicode character, excluding the surrogate blocks, FFFE and FFFF."
        0x20 <= ord(char) <= 0xD7FF or
        0xE000 <= ord(char) <= 0xFFFD or
        0x10000 <= ord(char) <= 0x10FFFF
    )

    # Overwrite the file with the new contents.
    file_path.write_text(text)


if __name__ == "__main__":
    if len(sys.argv) < 2:
        print(f"Usage: {sys.argv[0]} <path>", file=sys.stderr)
        sys.exit(1)

    sys.exit(sanitize_xml(Path(sys.argv[1])))
