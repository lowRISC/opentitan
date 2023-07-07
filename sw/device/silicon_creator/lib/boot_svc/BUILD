# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

package(default_visibility = ["//visibility:public"])

cc_library(
    name = "boot_svc_header",
    srcs = ["boot_svc_header.c"],
    hdrs = ["boot_svc_header.h"],
    deps = [
        "//sw/device/silicon_creator/lib/base:chip",
        "//sw/device/silicon_creator/lib/drivers:hmac",
    ],
)

cc_test(
    name = "boot_svc_header_unittest",
    srcs = ["boot_svc_header_unittest.cc"],
    deps = [
        ":boot_svc_header",
        "//sw/device/silicon_creator/lib/base:chip",
        "//sw/device/silicon_creator/testing:rom_test",
        "@googletest//:gtest_main",
    ],
)
