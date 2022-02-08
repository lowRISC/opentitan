# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

package(default_visibility = ["//visibility:public"])

cc_library(
    name = "global_mock",
    testonly = True,
    hdrs = ["global_mock.h"],
)

cc_library(
    name = "testing",
    srcs = [
        "mock_mmio.cc",
        "//sw/device/lib/base:mmio_src",
    ],
    hdrs = [
        "mock_mmio.h",
        "mock_mmio_test_utils.h",
    ],
    defines = [
        "MOCK_MMIO=1",
    ],
    deps = [
        "//sw/device/lib/base",
        "@googletest//:gtest",
    ],
)

cc_test(
    name = "mock_mmio_test",
    srcs = [
        "mock_mmio_test.cc",
    ],
    defines = [
        "MOCK_MMIO=1",
    ],
    deps = [
        ":testing",
        "@googletest//:gtest_main",
    ],
)
