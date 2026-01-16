# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load(
    "//rules:cross_platform.bzl",
    "dual_cc_library",
    "dual_inputs",
)
load(
    "//rules/opentitan:defs.bzl",
    "EARLGREY_TEST_ENVS",
    "opentitan_test",
)
load(
    "//sw/device/silicon_creator/rom_ext:defs.bzl",
    "TEST_OWNER_CONFIGS",
)

package(default_visibility = ["//visibility:public"])

cc_library(
    name = "datatypes",
    hdrs = ["datatypes.h"],
    deps = [
        "//sw/device/lib/base:bitfield",
        "//sw/device/silicon_creator/lib:nonce",
        "//sw/device/silicon_creator/lib/sigverify:ecdsa_p256_key",
        "//sw/device/silicon_creator/lib/sigverify:spx_key",
    ],
)

cc_library(
    name = "isfb",
    srcs = ["isfb.c"],
    hdrs = ["isfb.h"],
    deps = [
        ":datatypes",
        ":owner_block",
        "//sw/device/lib/base:hardened",
        "//sw/device/lib/base:hardened_memory",
        "//sw/device/lib/base:macros",
        "//sw/device/silicon_creator/lib:error",
        "//sw/device/silicon_creator/lib:manifest",
        "//sw/device/silicon_creator/lib/drivers:flash_ctrl",
        "//sw/device/silicon_creator/lib/drivers:rnd",
    ],
)

cc_test(
    name = "isfb_unittest",
    srcs = [
        "isfb_unittest.cc",
    ],
    deps = [
        ":datatypes",
        ":isfb",
        ":owner_block",
        "//sw/device/lib/base:hardened",
        "//sw/device/silicon_creator/lib:manifest",
        "//sw/device/silicon_creator/lib/drivers:flash_ctrl",
        "//sw/device/silicon_creator/testing:rom_test",
        "@googletest//:gtest_main",
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
            ":owner_verify",
            "//sw/device/lib/arch:device",
            "//sw/device/lib/base:memory",
            "//sw/device/lib/base:hardened_memory",
            "//sw/device/silicon_creator/lib/drivers:rnd",
            "//sw/device/silicon_creator/lib/drivers:keymgr",
            "//sw/device/silicon_creator/lib/drivers:kmac",
            "//sw/device/silicon_creator/lib/drivers:flash_ctrl",
        ],
        host = [
            "//sw/device/lib/base:global_mock",
            "//sw/device/silicon_creator/testing:rom_test",
            "@googletest//:gtest",
        ],
        shared = [
            ":datatypes",
            "//sw/device/lib/base:hardened",
            "//sw/device/silicon_creator/lib/drivers:hmac",
            "//sw/device/silicon_creator/lib:error",
        ],
    ),
)

cc_library(
    name = "ownership",
    srcs = ["ownership.c"],
    hdrs = ["ownership.h"],
    deps = [
        ":datatypes",
        ":owner_block",
        ":ownership_activate",
        ":ownership_key",
        "//sw/device/lib/base:hardened_memory",
        "//sw/device/silicon_creator/lib:boot_data",
        "//sw/device/silicon_creator/lib:boot_log",
        "//sw/device/silicon_creator/lib:dbg_print",
        "//sw/device/silicon_creator/lib/base:sec_mmio",
        "//sw/device/silicon_creator/lib/drivers:flash_ctrl",
        "//sw/device/silicon_creator/lib/drivers:lifecycle",
        "//sw/device/silicon_creator/lib/drivers:rnd",
        "//sw/device/silicon_creator/lib/sigverify:flash_exec",
    ],
)

cc_test(
    name = "ownership_unittest",
    srcs = [
        "ownership_unittest.cc",
    ],
    deps = [
        ":datatypes",
        ":ownership",
        ":ownership_key",
        "//sw/device/lib/base:hardened",
        "//sw/device/silicon_creator/lib:boot_data",
        "//sw/device/silicon_creator/lib/boot_svc:boot_svc_header",
        "//sw/device/silicon_creator/testing:rom_test",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "owner_block",
    srcs = ["owner_block.c"],
    hdrs = ["owner_block.h"],
    deps = [
        ":datatypes",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:bitfield",
        "//sw/device/lib/base:hardened",
        "//sw/device/lib/base:hardened_memory",
        "//sw/device/silicon_creator/lib:boot_data",
        "//sw/device/silicon_creator/lib/base:chip",
        "//sw/device/silicon_creator/lib/drivers:flash_ctrl",
        "//sw/device/silicon_creator/lib/drivers:hmac",
        "//sw/device/silicon_creator/lib/drivers:pinmux",
        "//sw/device/silicon_creator/lib/drivers:rnd",
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
        ":owner_block",
        ":ownership_key",
        "//sw/device/lib/base:memory",
        "//sw/device/silicon_creator/lib:boot_data",
        "//sw/device/silicon_creator/lib:error",
        "//sw/device/silicon_creator/lib/boot_svc:boot_svc_msg",
        "//sw/device/silicon_creator/lib/drivers:flash_ctrl",
        "//sw/device/silicon_creator/lib/drivers:hmac",
        "//sw/device/silicon_creator/lib/drivers:lifecycle",
        "//sw/device/silicon_creator/lib/sigverify:flash_exec",
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
        "//sw/device/silicon_creator/lib/drivers:lifecycle",
        "//sw/device/silicon_creator/lib/drivers:rnd",
        "//sw/device/silicon_creator/lib/sigverify:flash_exec",
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
        ":owner_block",
        ":ownership_key",
        "//sw/device/lib/base:memory",
        "//sw/device/silicon_creator/lib:boot_data",
        "//sw/device/silicon_creator/lib:error",
        "//sw/device/silicon_creator/lib/boot_svc:boot_svc_msg",
        "//sw/device/silicon_creator/lib/drivers:flash_ctrl",
        "//sw/device/silicon_creator/lib/drivers:lifecycle",
        "//sw/device/silicon_creator/lib/sigverify:flash_exec",
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
        "//sw/device/silicon_creator/lib/sigverify:flash_exec",
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
        "//sw/device/silicon_creator/lib/boot_svc:boot_svc_msg",
        "//sw/device/silicon_creator/lib/drivers:flash_ctrl",
        "//sw/device/silicon_creator/lib/ownership/keys/fake:includes",
        "//sw/device/silicon_creator/lib/rescue",
    ],
    alwayslink = True,
)

[
    cc_library(
        name = "test_owner_{}".format(name),
        testonly = True,
        srcs = ["test_owner.c"],
        defines = param["owner_defines"],
        deps = [
            ":datatypes",
            ":owner_block",
            ":ownership",
            "//sw/device/silicon_creator/lib:boot_data",
            "//sw/device/silicon_creator/lib/boot_svc:boot_svc_msg",
            "//sw/device/silicon_creator/lib/drivers:flash_ctrl",
            "//sw/device/silicon_creator/lib/ownership/keys/fake:includes",
            "//sw/device/silicon_creator/lib/rescue",
        ],
        alwayslink = True,
    )
    for name, param in TEST_OWNER_CONFIGS.items()
]

dual_cc_library(
    name = "owner_verify",
    srcs = dual_inputs(
        device = ["owner_verify.c"],
        host = ["mock_owner_verify.cc"],
    ),
    hdrs = dual_inputs(
        host = ["mock_owner_verify.h"],
        shared = ["owner_verify.h"],
    ),
    deps = dual_inputs(
        device = [
            "//sw/device/silicon_creator/lib/sigverify",
        ],
        host = [
            "//sw/device/lib/base:global_mock",
            "//sw/device/silicon_creator/testing:rom_test",
            "@googletest//:gtest",
        ],
        shared = [
            ":datatypes",
            "//sw/device/silicon_creator/lib/base:util",
            "//sw/device/silicon_creator/lib/drivers:hmac",
            "//sw/device/silicon_creator/lib:error",
        ],
    ),
)

opentitan_test(
    name = "owner_verify_functest",
    srcs = ["owner_verify_functest.c"],
    exec_env = EARLGREY_TEST_ENVS,
    deps = [
        ":owner_verify",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)
