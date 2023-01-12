# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

package(default_visibility = ["//visibility:public"])

load(
    "//rules:opentitan_test.bzl",
    "opentitan_functest",
    "verilator_params",
)

opentitan_functest(
    name = "fors_test",
    srcs = ["fors_test.c"],
    verilator = verilator_params(
        timeout = "long",
    ),
    deps = [
        "//sw/device/lib/base:memory",
        "//sw/device/lib/runtime:ibex",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/lib:test_main",
        "//sw/device/silicon_creator/lib/sigverify/sphincsplus:context",
        "//sw/device/silicon_creator/lib/sigverify/sphincsplus:fors",
        "//sw/device/silicon_creator/lib/sigverify/sphincsplus:hash",
    ],
)

opentitan_functest(
    name = "wots_test",
    srcs = ["wots_test.c"],
    verilator = verilator_params(
        timeout = "long",
    ),
    deps = [
        "//sw/device/lib/base:memory",
        "//sw/device/lib/runtime:ibex",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/lib:test_main",
        "//sw/device/silicon_creator/lib/sigverify/sphincsplus:context",
        "//sw/device/silicon_creator/lib/sigverify/sphincsplus:hash",
        "//sw/device/silicon_creator/lib/sigverify/sphincsplus:wots",
    ],
)
