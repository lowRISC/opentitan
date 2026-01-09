# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# The ROM_EXT version number to encode into the manifest.
# NOTE: the version numbers are integers, but have to be encoded as strings
# because of how the bazel rule accepts attributes.
ROM_EXT_VERSION = struct(
    MAJOR = "0",
    MINOR = "105",
    SECURITY = "0",
)

ROM_EXT_VARIATIONS = {
    "dice_x509": [
        "//sw/device/silicon_creator/lib/cert:dice",
    ],
    "dice_cwt": [
        "//sw/device/silicon_creator/lib/cert:dice_cwt",
    ],
}

SLOTS = [
    "a",
    "b",
    "virtual",
]
