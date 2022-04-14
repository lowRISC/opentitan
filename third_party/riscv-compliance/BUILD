# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load(":defs.bzl", "TESTS", "rv_compliance_test")

package(default_visibility = ["//visibility:public"])

cc_library(
    name = "compliance_main",
    srcs = [
        "compliance_main.S",
        "compliance_main.c",
    ],
    linkopts = ["-Wl,--no-relax"],
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "@riscv-compliance//:riscv-test-env",
    ],
    alwayslink = True,
)

[[rv_compliance_test(test, arch) for test in tests] for arch, tests in TESTS.items()]
