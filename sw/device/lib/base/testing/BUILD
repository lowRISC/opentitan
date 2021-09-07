# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

package(default_visibility = ["//visibility:public"]) 

cc_library(
    name = "mock_mmio",
    linkstatic = True,
    srcs = [
        "mock_mmio.cc",
        "mock_mmio.h",
        "mock_mmio_test_utils.h",
        ],
    deps = [
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/base:bitfield",
        "@googletest//:gtest",
        ],
    copts = ["-DMOCK_MMIO"],
    )

cc_test(
  name = "mock_mmio_test",
  srcs = [
      "mock_mmio_test.cc",
      ],
  deps = [
      "@googletest//:gtest_main",
      ":mock_mmio",
      ],
      copts = [
          "-DMOCK_MMIO",
          ],
    )
