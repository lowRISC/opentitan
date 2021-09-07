# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

cc_library(
  name = "clkmgr",
  srcs = [
      ":dif_clkmgr.c",
      ":dif_clkmgr.h",
      ":dif_warn_unused_result.h",
      ],
  deps = [
      "//sw/device/lib/base:mmio",
      "//hw/top_earlgrey/ip/clkmgr/data/autogen:clkmgr_regs",
      ],
  )

cc_test(
  name = "clkmgr_unittest",
  srcs = [
      ":dif_clkmgr_unittest.cc",
      ],
  deps = [
      ":clkmgr",
      "//hw/top_earlgrey/ip/clkmgr/data/autogen:clkmgr_regs",
      "@googletest//:gtest_main",
      "//sw/device/lib/base:mmio",
      "//sw/device/lib/base/testing:mock_mmio",
      ],
  copts = [
      "-DMOCK_MMIO",
      ],
  )

