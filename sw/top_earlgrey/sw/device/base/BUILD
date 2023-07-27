# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load(
    "//rules:opentitan_test.bzl",
    "cw310_params",
    "opentitan_functest",
)

package(default_visibility = ["//visibility:public"])

opentitan_functest(
    name = "memory_perftest",
    srcs = ["//sw/lib/sw/device/base:memory_perftest_c"],
    cw310 = cw310_params(
        tags = [
            "flaky",
            "manual",
        ],
    ),
    manifest = "//sw/device/silicon_creator/rom_ext:manifest_standard",
    targets = ["cw310_test_rom"],
    deps = [
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/lib/sw/device/base:macros",
        "//sw/lib/sw/device/base:memory",
        "//sw/lib/sw/device/runtime:ibex",
        "//sw/lib/sw/device/runtime:log",
        "//sw/top_earlgrey/sw/device/runtime:print",
    ],
)
