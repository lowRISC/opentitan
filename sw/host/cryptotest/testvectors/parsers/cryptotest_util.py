# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

def parse_rsp(file_path: str) -> dict:
    """Parser for NIST `.rsp` files.

    NIST response files (.rsp) provide the expected results of cryptographic
    operations. No formal standard exists for these files, but they generally take
    the following format:
      - Each file contains zero or more sections. The start of each section is
          denoted by a line beginning with "[" and ending with "]". The text between
          the brackets is the title of the section.
      - Each section contains at least one entry where an entry is a collection of
        key-value pairs. Entries are separated from each other by an empty line.
      - A line that starts with a "#" is a comment and is ignored.
    """
    result = dict()
    curr_section = list()
    curr_section_name = ""
    curr_entry = dict()
    with open(file_path, "r") as file:
        for line_num, line in enumerate(file):
            line = line.strip()
            if line.startswith("#"):
                continue
            elif line.startswith("["):
                # Store the previous section and start a new section
                if curr_section:
                    result[curr_section_name] = curr_section
                    curr_section = list()
                curr_section_name = line.strip("[]")
            elif line == "":
                # Store the previous entry and start a new entry
                if curr_entry:
                    curr_section.append(curr_entry)
                    curr_entry = dict()
            elif line and "=" in line:
                # Append the key-value pair to the current entry
                key, value = [s.strip() for s in line.split("=", maxsplit=1)]
                if key in curr_entry.keys():
                    raise SyntaxError(f"Line {line_num}: Duplicate key ({key}) in entry")
                curr_entry[key] = value

        # If there is no newline at the end of the rsp file, then append the
        # last entry to the section
        if curr_entry:
            curr_section.append(curr_entry)
        # Append the last section to the result
        result[curr_section_name] = curr_section
    return result


def str_to_byte_array(s: str) -> list:
    """
    Converts a string of hex digits to a list of bytes.

    The string is interpreted as a list of bytes from left to right.
    For example, str_to_byte_array("01020a0b") -> [1, 2, 10, 11]
    """
    if s.startswith("0x"):
        s = s[1:]
    if len(s) % 2 != 0:
        raise ValueError(f"String {s} has an odd number of digits; cannot convert into byte array.")

    byte_array = list()
    for i in range(0, len(s), 2):
        byte_array.append(int(s[i:i + 2], 16))
    return byte_array
