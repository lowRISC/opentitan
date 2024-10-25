# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

def secver_write_selection():
    """Return the secver_write value based on the configuration setting."""
    return select({
        "//sw/device/silicon_creator/rom_ext:secver_write_true": True,
        "//sw/device/silicon_creator/rom_ext:secver_write_false": False,
    })

# The ROM_EXT version number to encode into the manifest.
# NOTE: the version numbers are integers, but have to be encoded as strings
# because of how the bazel rule accepts attributes.
ROM_EXT_VERSION = struct(
    MAJOR = "0",
    MINOR = "6",
    SECURITY = "6",
)

SLOTS = [
    "a",
    "b",
    "virtual",
]
