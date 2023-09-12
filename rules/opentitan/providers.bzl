# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Providers and helper functions associated with all execution environments.

Cw310BinaryInfo = provider(
    doc = "CW310 Binary Info",
)

SimDvBinaryInfo = provider(
    doc = "Dv Binary Info",
)

SimVerilatorBinaryInfo = provider(
    doc = "Verilator Binary Info",
)

ALL_BINARY_PROVIDERS = [
    Cw310BinaryInfo,
    SimDvBinaryInfo,
    SimVerilatorBinaryInfo,
]

def get_binary_files(attrs):
    """Get the list of binary files associated with a list of labels.

    Args:
      attrs: a list of labels with BinaryInfo or DefaultInfo providers.
    Returns:
      List[File]: the files associated with the labels.
    """
    files = []
    for attr in attrs:
        found_files = False
        for p in ALL_BINARY_PROVIDERS:
            if p in attr:
                found_files = True
                files.append(attr[p].binary)

        if not found_files and DefaultInfo in attr:
            found_files = True
            files.extend(attr[DefaultInfo].files.to_list())
        if not found_files:
            print("No file providers in ", attr)
    return files
