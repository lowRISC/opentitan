# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

package(default_visibility = ["//visibility:public"])

cc_library(
    name = "global_mock",
    hdrs = ["global_mock.h"],
)

cc_library(
    name = "mock_mmio",
    srcs = ["mock_mmio.cc"],
    hdrs = [
        "mock_mmio.h",
        "mock_mmio_test_utils.h",
    ],
    defines = [
        "MOCK_MMIO=1",
    ],
    deps = [
        "//sw/device/lib/base:mmio",
        "@googletest//:gtest",
    ],
)

cc_library(
    name = "mock_abs_mmio",
    testonly = True,
    hdrs = [
        "mock_abs_mmio.h",
        "mock_mmio_test_utils.h",
    ],
    defines = ["MOCK_ABS_MMIO"],
    deps = [
        ":global_mock",
        ":mock_mmio",
        "//sw/device/lib/base:abs_mmio",
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
        ":mock_mmio",
        "@googletest//:gtest_main",
    ],
)
