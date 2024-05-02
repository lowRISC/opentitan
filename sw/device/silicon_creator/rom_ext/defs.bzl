# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# The ROM_EXT version number to encode into the manifest.
# NOTE: the version numbers are integers, but have to be encoded as strings
# because of how the bazel rule accepts attributes.
ROM_EXT_VERSION = struct(
    MAJOR = "0",
    MINOR = "1",
    SECURITY = "0",
)
