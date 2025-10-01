# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

package(default_visibility = ["//visibility:public"])

load("//rules/opentitan:defs.bzl", "OPENTITAN_CPU")
load("//rules/coverage:asm.bzl", "asm_library_with_coverage")

asm_library_with_coverage(
    name = "crt",
    srcs = ["crt.S"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        "//sw/device/lib/coverage:api_asm",
    ],
)
