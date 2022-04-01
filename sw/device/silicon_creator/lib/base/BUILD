# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:opentitan.bzl", "OPENTITAN_CPU")
load("//rules:cross_platform.bzl", "dual_cc_device_library_of", "dual_cc_library", "dual_inputs")

package(default_visibility = ["//visibility:public"])

exports_files([
    "static_critical.ld",
    "mock_csr.h",
    "mock_csr.cc",
    "mock_csr_test.cc",
])

dual_cc_library(
    name = "sec_mmio",
    srcs = dual_inputs(
        device = ["sec_mmio.c"],
        host = ["mock_sec_mmio.cc"],
    ),
    hdrs = dual_inputs(
        host = ["mock_sec_mmio.h"],
        shared = ["sec_mmio.h"],
    ),
    deps = dual_inputs(
        host = [
            "//sw/device/lib/base/testing:global_mock",
            "//sw/device/silicon_creator/testing:mask_rom_test",
            "@googletest//:gtest",
        ],
        shared = [
            "//sw/device/lib/base:mmio",
            "//sw/device/lib/base:abs_mmio",
            "//sw/device/lib/base:hardened",
            "//sw/device/lib/base:macros",
            "//sw/device/silicon_creator/lib:error",
        ],
    ),
)

cc_test(
    name = "sec_mmio_unittest",
    srcs = ["sec_mmio_unittest.cc"],
    deps = [
        dual_cc_device_library_of(":sec_mmio"),
        "//sw/device/silicon_creator/testing:mask_rom_test",
        "@googletest//:gtest_main",
    ],
)
