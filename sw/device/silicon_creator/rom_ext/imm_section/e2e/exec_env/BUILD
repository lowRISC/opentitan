# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_python//python:defs.bzl", "py_test")
load(
    "//sw/device/silicon_creator/rom_ext:defs.bzl",
    "SLOTS",
)

package(default_visibility = ["//visibility:public"])

[
    py_test(
        name = "env_independent_slot_{}_test".format(slot),
        srcs = ["env_independent_test.py"],
        data = [
            "//sw/device/silicon_creator/rom_ext/imm_section:main_binaries_slot_{}".format(slot),
        ],
        main = "env_independent_test.py",
    )
    for slot in SLOTS
]
