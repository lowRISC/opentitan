# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_python//python:defs.bzl", "py_test")
load(
    "//sw/device/silicon_creator/rom_ext:defs.bzl",
    "ROM_EXT_VARIATIONS",
    "SLOTS",
)

package(default_visibility = ["//visibility:public"])

[
    py_test(
        name = "env_independent_{}_slot_{}_test".format(variation, slot),
        srcs = ["env_independent_test.py"],
        data = [
            "//sw/device/silicon_creator/rom_ext/imm_section:main_binaries_{}_slot_{}".format(variation, slot),
        ],
        main = "env_independent_test.py",
        # The imm_section varies in coverage mode because of the build ID.
        tags = ["coverage_broken"],
    )
    for slot in SLOTS
    for variation in ROM_EXT_VARIATIONS.keys()
]
