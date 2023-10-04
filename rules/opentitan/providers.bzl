# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Providers and helper functions associated with all execution environments.

Cw310BinaryInfo = provider(
    doc = "CW310 Binary Info",
)

Cw305BinaryInfo = provider(
    doc = "CW305 Binary Info",
)

Cw340BinaryInfo = provider(
    doc = "CW340 Binary Info",
)

SimDvBinaryInfo = provider(
    doc = "Dv Binary Info",
)

SimVerilatorBinaryInfo = provider(
    doc = "Verilator Binary Info",
)

ALL_BINARY_PROVIDERS = [
    Cw310BinaryInfo,
    Cw340BinaryInfo,
    SimDvBinaryInfo,
    SimVerilatorBinaryInfo,
]

def get_binary_files(attrs, field = "binary", providers = ALL_BINARY_PROVIDERS):
    """Get the list of binary files associated with a list of labels.

    Args:
      attrs: a list of labels with BinaryInfo or DefaultInfo providers.
      field: the name of the provider field contaning files.
      providers: the set of providers to inspect.
    Returns:
      List[File]: the files associated with the labels.
    """
    files = []
    for attr in attrs:
        found_files = False
        for p in providers:
            if p in attr:
                found_files = True
                files.append(getattr(attr[p], field))

        if not found_files and DefaultInfo in attr:
            found_files = True
            files.extend(attr[DefaultInfo].files.to_list())
        if not found_files:
            print("No file providers in ", attr)
    return files

def get_one_binary_file(attr, field = "binary", providers = ALL_BINARY_PROVIDERS):
    """Get exactly one binary file associated with a label.

    Args:
      attr: a label with BinaryInfo or DefaultInfo providers.
      field: the name of the provider field contaning files.
      providers: the set of providers to inspect.
    Returns:
      File: the files associated with the label.
    """
    files = get_binary_files([attr], field, providers)
    if len(files) != 1:
        fail("Expected only one binary file in", attr)
    return files[0]
