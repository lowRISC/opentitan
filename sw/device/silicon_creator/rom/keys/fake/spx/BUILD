# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

package(default_visibility = ["//visibility:public"])

cc_library(
    name = "spx",
    srcs = [
        "sigverify_spx_keys_fake.c",
        "//sw/device/silicon_creator/rom:sigverify_keys.h",
        "//sw/device/silicon_creator/rom:sigverify_keys_spx.h",
    ],
    hdrs = [
        "dev_key_0_spx.h",
        "dev_key_1_spx.h",
        "prod_key_0_spx.h",
        "prod_key_1_spx.h",
        "prod_key_2_spx.h",
        "test_key_0_spx.h",
        "test_key_1_spx.h",
    ],
    deps = [
        "//sw/device/silicon_creator/rom:sigverify_key_types",
        "//sw/lib/sw/device/base:macros",
        "//sw/lib/sw/device/silicon_creator/sigverify",
    ],
)

cc_test(
    name = "spx_unittest",
    srcs = ["sigverify_spx_keys_fake_unittest.cc"],
    deps = [
        ":spx",
        "//hw/top_darjeeling/sw/autogen:top_darjeeling",
        "//sw/device/silicon_creator/rom:sigverify_keys",
        "//sw/device/silicon_creator/rom/keys/fake/rsa",
        "//sw/lib/sw/device/silicon_creator/testing:rom_test",
        "@googletest//:gtest_main",
    ],
)

filegroup(
    name = "test_key_0_spx",
    srcs = ["test_key_0_spx.pem"],
)

filegroup(
    name = "test_key_1_spx",
    srcs = ["test_key_1_spx.pem"],
)

filegroup(
    name = "dev_key_0_spx",
    srcs = ["dev_key_0_spx.pem"],
)

filegroup(
    name = "dev_key_1_spx",
    srcs = ["dev_key_1_spx.pem"],
)

filegroup(
    name = "prod_key_0_spx",
    srcs = ["prod_key_0_spx.pem"],
)

filegroup(
    name = "prod_key_1_spx",
    srcs = ["prod_key_1_spx.pem"],
)

filegroup(
    name = "prod_key_2_spx",
    srcs = ["prod_key_2_spx.pem"],
)
