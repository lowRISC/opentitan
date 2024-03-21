# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load(
    "//rules/opentitan:defs.bzl",
    "EARLGREY_TEST_ENVS",
    "cw310_params",
    "fpga_params",
    "opentitan_test",
    "verilator_params",
)
load(
    "//rules:cross_platform.bzl",
    "dual_cc_device_library_of",
    "dual_cc_library",
    "dual_inputs",
)

package(default_visibility = ["//visibility:public"])

cc_library(
    name = "datatypes",
    hdrs = ["datatypes.h"],
    deps = [
        "//sw/device/lib/base:bitfield",
        "//sw/device/silicon_creator/lib/sigverify:ecdsa_p256_key",
        "//sw/device/silicon_creator/lib/sigverify:rsa_key",
        "//sw/device/silicon_creator/lib/sigverify:spx_key",
    ],
)

cc_library(
    name = "ecdsa",
    srcs = ["ecdsa.c"],
    hdrs = ["ecdsa.h"],
    defines = [
        "USE_OTBN=1",
        #"USE_CRYPTOC=1",
    ],
    deps = [
        ":datatypes",
        "//sw/device/lib/base:hardened",
        "//sw/device/lib/base:hardened_memory",
        "//sw/device/lib/base:macros",
        "//sw/device/silicon_creator/lib:error",
        "//sw/device/silicon_creator/lib/drivers:hmac",
        "//sw/device/silicon_creator/lib:otbn_boot_services",
        #"//sw/vendor:cryptoc",
    ],
)

opentitan_test(
    name = "ecdsa_functest",
    srcs = ["ecdsa_functest.c"],
    exec_env = {
        "//hw/top_earlgrey:fpga_cw310_rom_with_fake_keys": None,
    },
    deps = [
        ":ecdsa",
        "//sw/device/lib/base:hardened",
        "//sw/device/lib/base:status",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:entropy_testutils",
        "//sw/device/lib/testing:hexstr",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/lib/ownership/keys/fake",
    ],
)

dual_cc_library(
    name = "ownership_key",
    srcs = dual_inputs(
        device = ["ownership_key.c"],
        host = ["mock_ownership_key.cc"],
    ),
    hdrs = dual_inputs(
        host = ["mock_ownership_key.h"],
        shared = ["ownership_key.h"],
    ),
    deps = dual_inputs(
        device = [
            ":ecdsa",
        ],
        host = [
            "//sw/device/lib/base:global_mock",
            "//sw/device/silicon_creator/testing:rom_test",
            "@googletest//:gtest",
        ],
        shared = [
            ":datatypes",
            "//sw/device/lib/base:hardened",
        ],
    ),
)

cc_library(
    name = "ownership",
    srcs = ["ownership.c"],
    hdrs = ["ownership.h"],
    deps = [
        ":datatypes",
        ":ecdsa",
        ":owner_block",
        ":ownership_key",
        "//sw/device/lib/base:hardened_memory",
        "//sw/device/silicon_creator/lib:boot_data",
        "//sw/device/silicon_creator/lib:dbg_print",
        "//sw/device/silicon_creator/lib/drivers:flash_ctrl",
    ],
)

cc_library(
    name = "owner_block",
    srcs = ["owner_block.c"],
    hdrs = ["owner_block.h"],
    deps = [
        ":datatypes",
        "//sw/device/lib/base:bitfield",
        "//sw/device/lib/base:hardened",
        "//sw/device/silicon_creator/lib:boot_data",
        "//sw/device/silicon_creator/lib/drivers:flash_ctrl",
    ],
)

cc_test(
    name = "owner_block_unittest",
    srcs = [
        "owner_block_unittest.cc",
        "testdata/basic_owner_testdata.h",
    ],
    deps = [
        ":datatypes",
        ":owner_block",
        "//sw/device/lib/base:bitfield",
        "//sw/device/lib/testing:binary_blob",
        "//sw/device/silicon_creator/lib:boot_data",
        "//sw/device/silicon_creator/testing:rom_test",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "ownership_unlock",
    srcs = ["ownership_unlock.c"],
    hdrs = ["ownership_unlock.h"],
    deps = [
        ":datatypes",
        ":ownership",
        ":ownership_key",
        "//sw/device/lib/base:memory",
        "//sw/device/silicon_creator/lib:boot_data",
        "//sw/device/silicon_creator/lib:error",
        "//sw/device/silicon_creator/lib/boot_svc:boot_svc_msg",
        "//sw/device/silicon_creator/lib/drivers:flash_ctrl",
        "//sw/device/silicon_creator/lib/drivers:hmac",
    ],
)

cc_test(
    name = "ownership_unlock_unittest",
    srcs = [
        "ownership_unlock_unittest.cc",
    ],
    deps = [
        ":datatypes",
        ":ownership_key",
        ":ownership_unlock",
        "//sw/device/lib/base:hardened",
        "//sw/device/silicon_creator/lib:boot_data",
        "//sw/device/silicon_creator/lib/boot_svc:boot_svc_header",
        "//sw/device/silicon_creator/testing:rom_test",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "ownership_activate",
    srcs = ["ownership_activate.c"],
    hdrs = ["ownership_activate.h"],
    deps = [
        ":datatypes",
        ":ownership",
        ":ownership_key",
        "//sw/device/lib/base:memory",
        "//sw/device/silicon_creator/lib:boot_data",
        "//sw/device/silicon_creator/lib:error",
        "//sw/device/silicon_creator/lib/boot_svc:boot_svc_msg",
        "//sw/device/silicon_creator/lib/drivers:flash_ctrl",
    ],
)

cc_test(
    name = "ownership_activate_unittest",
    srcs = [
        "ownership_activate_unittest.cc",
    ],
    deps = [
        ":datatypes",
        ":ownership_activate",
        ":ownership_key",
        "//sw/device/lib/base:hardened",
        "//sw/device/silicon_creator/lib:boot_data",
        "//sw/device/silicon_creator/lib/boot_svc:boot_svc_header",
        "//sw/device/silicon_creator/testing:rom_test",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "test_owner",
    testonly = True,
    srcs = ["test_owner.c"],
    deps = [
        ":datatypes",
        ":owner_block",
        ":ownership",
        "//sw/device/silicon_creator/lib:boot_data",
        "//sw/device/silicon_creator/lib/drivers:flash_ctrl",
        "//sw/device/silicon_creator/lib/ownership/keys/fake:includes",
    ],
    alwayslink = True,
)
