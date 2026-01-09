# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:files.bzl", "copy_files")

package(default_visibility = ["//visibility:public"])

# Add silicon binary targets once available.

copy_files(
    name = "copy_signed",
    testonly = True,
    srcs = [
        "//sw/device/silicon_creator/rom_ext/sival:signed",
    ],
    relative_to = ":BUILD",
    tags = ["manual"],
)
