# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
load("//rules:opentitan.bzl", "OPENTITAN_CPU")

package(default_visibility = ["//visibility:public"])
exports_files([
    "static_critical.ld",
    "mock_csr.h",
    "mock_csr.cc",
    "mock_csr_test.cc",
])

cc_library(
    name = "sec_mmio",
    srcs = ["sec_mmio.c"],
    hdrs = ["sec_mmio.h"],
    deps = [
        "//sw/device/lib/base:abs_mmio",
        "//sw/device/lib/base:hardened",
        "//sw/device/lib/base:macros",
        "//sw/device/silicon_creator/lib:error",
    ],
)

cc_library(
    name = "mock_sec_mmio",
    testonly = True,
    hdrs = [
        "mock_sec_mmio.h",
        "sec_mmio.h",
    ],
    deps = [
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/base/testing:global_mock",
        "//sw/device/silicon_creator/testing:mask_rom_test",
        "@googletest//:gtest",
    ],
)

cc_test(
    name = "sec_mmio_unittest",
    srcs = [
        "sec_mmio.c",
        "sec_mmio.h",
        "sec_mmio_unittest.cc",
    ],
    defines = ["OT_OFF_TARGET_TEST"],
    deps = [
        "//sw/device/lib/base:hardened",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:abs_mmio",
        "//sw/device/silicon_creator/lib:error",
        "//sw/device/silicon_creator/testing:mask_rom_test",
        "@googletest//:gtest_main",
    ],
)
