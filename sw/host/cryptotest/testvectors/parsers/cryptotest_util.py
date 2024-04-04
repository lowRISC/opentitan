# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

def parse_rsp(file_path: str, persists: list[str] = []) -> dict:
    """Parser for NIST `.rsp` files.

    NIST response files (.rsp) provide the expected results of cryptographic
    operations. No formal standard exists for these files, but they generally take
    the following format:
      - Lines beginning with a "[" are headers. Headers contain either a bare name,
        like "Section Name", a single key-value pair, like "Hash = SHA-256", or a
        list of strings, like "RSA-2048, SHA-256".
      - A line that starts with a "#" is a comment and is ignored.
      - Other non-blank lines contain a single key-value pair.
    Due to the heterogeneity of these files, this function applies multiple complex
    rules to parse the content into a set of test vectors:
      - Some key-value pairs are applied to multiple test cases. These include the
        key-value pairs in headers, as well as those with keys specified in the
        argument array `persists`.
      - A group of non-header key-value pair lines (delimited by newlines or a header
        line) constitutes a test case if it does not contain any keys in `persists`.
      - If a group of non-header key-value pair lines contains the same key multiple
        times without a newline in between, all of their associated values will be
        kept in a list.
    """
    persistent_variables = {}
    test_cases = []
    test_case = None
    exclude_group = False
    group_variables = []
    with open(file_path, "r") as file:
        for line_num, line in enumerate(file):
            line = line.strip()
            # Ignore comments
            if line.startswith("#"):
                continue
            elif line.startswith("["):
                # We have a header. If the header is a single title, store
                # it as the section name. If it is a key-value pair, store
                # the pair in our set of persistent variables.

                # If we were working on a test case, add it.
                if test_case is not None:
                    if not exclude_group:
                        test_cases.append(test_case)
                    test_case = None
                    group_variables = []
                    exclude_group = False
                header_text = line.strip("[]")
                kv = [s.strip() for s in header_text.split("=", maxsplit=1)]
                if len(kv) == 1:
                    # We don't have a key-value pair. See if we have a CSV list.
                    csv = [s.strip() for s in header_text.split(",")]
                    if len(csv) == 1:
                        # Just a name. Store it as a string.
                        persistent_variables["section_name"] = header_text
                    else:
                        # We have a CSV list. Store it as an array.
                        persistent_variables["section_name"] = csv
                else:
                    # We have a key-value pair to store.
                    persistent_variables[kv[0]] = kv[1]
            elif line == "":
                # We are staring a new group. Add the test case if we have one,
                # and clear our list of variables for the current group.
                if test_case is not None and not exclude_group:
                    test_cases.append(test_case)
                test_case = None
                group_variables = []
                exclude_group = False
            elif line and "=" in line:
                if test_case is None:
                    test_case = persistent_variables.copy()
                # Get the key and value
                key, value = [s.strip() for s in line.split("=", maxsplit=1)]
                d = test_case
                # If we have a variable intended to persist, store it properly and
                # remember the current group does not constitute a test case.
                if key in persists:
                    d = persistent_variables
                    exclude_group = True
                if key in group_variables:
                    # We've already seen this variable in the current group. Store all
                    # the values in a list.
                    if type(d[key]) == str:
                        d[key] = [d[key], value]
                    else:
                        d[key].append(value)
                else:
                    # We haven't seen this variable yet in the current
                    # group. Store its value and remember we've seen
                    # it.
                    d[key] = value
                    group_variables.append(key)

        # If there is no newline at the end of the rsp file, then append the
        # last entry to the section
        if test_case is not None:
            test_cases.append(test_case)
    return test_cases


def str_to_byte_array(s: str) -> list:
    """
    Converts a string of hex digits to a list of bytes.

    The string is interpreted as a list of bytes from left to right.
    For example, str_to_byte_array("01020a0b") -> [1, 2, 10, 11]
    """
    if s.startswith("0x"):
        s = s[2:]
    if len(s) % 2 != 0:
        s = "0" + s

    byte_array = list()
    for i in range(0, len(s), 2):
        byte_array.append(int(s[i:i + 2], 16))
    return byte_array
