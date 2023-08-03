# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:cross_platform.bzl", "dual_cc_device_library_of", "dual_cc_library", "dual_inputs")

package(default_visibility = ["//visibility:public"])

dual_cc_library(
    name = "boot_svc_header",
    srcs = dual_inputs(
        device = ["boot_svc_header.c"],
        host = ["mock_boot_svc_header.cc"],
    ),
    hdrs = dual_inputs(
        host = ["mock_boot_svc_header.h"],
        shared = ["boot_svc_header.h"],
    ),
    deps = dual_inputs(
        host = [
            "//sw/device/lib/base:global_mock",
            "//sw/device/silicon_creator/testing:rom_test",
            "@googletest//:gtest",
        ],
        shared = [
            "//sw/device/silicon_creator/lib/base:chip",
            "//sw/device/silicon_creator/lib/drivers:hmac",
        ],
    ),
)

cc_test(
    name = "boot_svc_header_unittest",
    srcs = ["boot_svc_header_unittest.cc"],
    deps = [
        dual_cc_device_library_of(":boot_svc_header"),
        "//sw/device/silicon_creator/lib/base:chip",
        "//sw/device/silicon_creator/testing:rom_test",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "boot_svc_empty",
    srcs = ["boot_svc_empty.c"],
    hdrs = ["boot_svc_empty.h"],
    deps = [
        ":boot_svc_header",
        "//sw/device/lib/base:macros",
        "//sw/device/silicon_creator/lib/base:chip",
        "//sw/device/silicon_creator/lib/drivers:rnd",
    ],
)

cc_library(
    name = "boot_svc_primary_bl0_slot",
    srcs = ["boot_svc_primary_bl0_slot.c"],
    hdrs = ["boot_svc_primary_bl0_slot.h"],
    deps = [
        ":boot_svc_header",
        "//sw/device/lib/base:macros",
        "//sw/device/silicon_creator/lib:boot_data",
        "//sw/device/silicon_creator/lib:error",
        "//sw/device/silicon_creator/lib/base:chip",
    ],
)

cc_test(
    name = "boot_svc_primary_bl0_slot_unittest",
    srcs = ["boot_svc_primary_bl0_slot_unittest.cc"],
    deps = [
        ":boot_svc_primary_bl0_slot",
        "//sw/device/silicon_creator/lib:boot_data",
        "//sw/device/silicon_creator/lib:error",
        "//sw/device/silicon_creator/testing:rom_test",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "boot_svc_min_bl0_sec_ver",
    srcs = ["boot_svc_min_bl0_sec_ver.c"],
    hdrs = ["boot_svc_min_bl0_sec_ver.h"],
    deps = [
        ":boot_svc_header",
        "//sw/device/lib/base:macros",
        "//sw/device/silicon_creator/lib:boot_data",
        "//sw/device/silicon_creator/lib:error",
        "//sw/device/silicon_creator/lib/base:chip",
    ],
)

cc_test(
    name = "boot_svc_min_bl0_sec_ver_unittest",
    srcs = ["boot_svc_min_bl0_sec_ver_unittest.cc"],
    deps = [
        ":boot_svc_min_bl0_sec_ver",
        "//sw/device/silicon_creator/lib:boot_data",
        "//sw/device/silicon_creator/lib:error",
        "//sw/device/silicon_creator/testing:rom_test",
        "@googletest//:gtest_main",
    ],
)

cc_test(
    name = "boot_svc_empty_unittest",
    srcs = ["boot_svc_empty_unittest.cc"],
    deps = [
        ":boot_svc_empty",
        "//sw/device/silicon_creator/testing:rom_test",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "boot_svc_msg",
    hdrs = ["boot_svc_msg.h"],
    deps = [
        ":boot_svc_empty",
        ":boot_svc_header",
        ":boot_svc_min_bl0_sec_ver",
        ":boot_svc_next_boot_bl0_slot",
        "//sw/device/lib/base:macros",
    ],
)

cc_library(
    name = "boot_svc_next_boot_bl0_slot",
    srcs = ["boot_svc_next_boot_bl0_slot.c"],
    hdrs = ["boot_svc_next_boot_bl0_slot.h"],
    deps = [
        ":boot_svc_header",
        "//sw/device/lib/base:macros",
        "//sw/device/silicon_creator/lib:error",
        "//sw/device/silicon_creator/lib/base:chip",
    ],
)

cc_test(
    name = "boot_svc_next_boot_bl0_slot_unittest",
    srcs = ["boot_svc_next_boot_bl0_slot_unittest.cc"],
    deps = [
        ":boot_svc_next_boot_bl0_slot",
        "//sw/device/silicon_creator/testing:rom_test",
        "@googletest//:gtest_main",
    ],
)
