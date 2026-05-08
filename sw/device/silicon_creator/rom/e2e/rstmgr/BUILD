# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules/opentitan:defs.bzl", "fpga_params", "opentitan_test")
load(
    "//rules:const.bzl",
    "CONST",
)
load(
    "//rules:otp.bzl",
    "STD_OTP_OVERLAYS",
    "otp_hex",
    "otp_image",
    "otp_json",
    "otp_partition",
)

package(default_visibility = ["//visibility:public"])

otp_json(
    name = "otp_json_cpu_info_enabled",
    partitions = [
        otp_partition(
            name = "OWNER_SW_CFG",
            items = {
                "OWNER_SW_CFG_ROM_RSTMGR_INFO_EN": otp_hex(CONST.HARDENED_BYTE_TRUE << 8),
            },
        ),
    ],
)

otp_image(
    name = "otp_img_cpu_info_enabled",
    src = "//hw/top_earlgrey/data/otp:otp_json_rma",
    overlays = STD_OTP_OVERLAYS + [":otp_json_cpu_info_enabled"],
)

CPU_INFO_TESTCASES = [
    {
        "name": "disabled",
        "fpga": fpga_params(),
        "defines": ["TEST_CPU_INFO_DISABLED"],
    },
    {
        "name": "enabled",
        "fpga": fpga_params(
            otp = ":otp_img_cpu_info_enabled",
        ),
        "defines": ["TEST_CPU_INFO_ENABLED"],
    },
]

[
    opentitan_test(
        name = "cpu_info_{}_test".format(testcase["name"]),
        srcs = ["cpu_info_test.c"],
        exec_env = {
            "//hw/top_earlgrey:fpga_cw310_rom_with_fake_keys": None,
            "//hw/top_earlgrey:fpga_cw340_rom_with_fake_keys": None,
        },
        fpga = testcase["fpga"],
        local_defines = testcase["defines"],
        deps = [
            "//hw/top:rstmgr_c_regs",
            "//sw/device/lib/base:macros",
            "//sw/device/lib/base:mmio",
            "//sw/device/lib/dif:rv_core_ibex",
            "//sw/device/lib/runtime:log",
            "//sw/device/lib/testing:rv_core_ibex_testutils",
            "//sw/device/lib/testing/test_framework:check",
            "//sw/device/lib/testing/test_framework:ottf_main",
            "//sw/device/silicon_creator/lib:error",
            "//sw/device/silicon_creator/lib/drivers:retention_sram",
            "//sw/device/silicon_creator/lib/drivers:rstmgr",
        ],
    )
    for testcase in CPU_INFO_TESTCASES
]

otp_json(
    name = "otp_json_alert_info_enabled",
    partitions = [
        otp_partition(
            name = "OWNER_SW_CFG",
            items = {
                "OWNER_SW_CFG_ROM_RSTMGR_INFO_EN": otp_hex(CONST.HARDENED_BYTE_TRUE << 0),
            },
        ),
    ],
)

otp_image(
    name = "otp_img_alert_info_enabled",
    src = "//hw/top_earlgrey/data/otp:otp_json_rma",
    overlays = STD_OTP_OVERLAYS + [
        ":otp_json_alert_info_enabled",
        "//sw/device/silicon_creator/rom/e2e/shutdown_alert:shutdown_alert_owner_sw_cfg",
        "//sw/device/silicon_creator/rom/e2e/shutdown_alert:shutdown_alert_digest_cfg",
    ],
)

ALERT_INFO_TESTCASES = [
    {
        "name": "disabled",
        "fpga": fpga_params(
            otp = "//sw/device/silicon_creator/rom/e2e/shutdown_alert:otp_img_shutdown_alert_rma",
        ),
        "defines": ["TEST_ALERT_INFO_DISABLED"],
    },
    {
        "name": "enabled",
        "fpga": fpga_params(
            otp = ":otp_img_alert_info_enabled",
        ),
        "defines": ["TEST_ALERT_INFO_ENABLED"],
    },
]

[
    opentitan_test(
        name = "alert_info_{}_test".format(testcase["name"]),
        srcs = ["alert_info_test.c"],
        exec_env = {
            "//hw/top_earlgrey:fpga_cw310_rom_with_fake_keys": None,
            "//hw/top_earlgrey:fpga_cw340_rom_with_fake_keys": None,
        },
        fpga = testcase["fpga"],
        local_defines = testcase["defines"],
        deps = [
            "//hw/top:uart_c_regs",
            "//hw/top/dt",
            "//hw/top_earlgrey/sw/autogen:top_earlgrey",
            "//sw/device/lib/base:abs_mmio",
            "//sw/device/lib/base:macros",
            "//sw/device/lib/runtime:log",
            "//sw/device/lib/testing/test_framework:check",
            "//sw/device/lib/testing/test_framework:ottf_main",
            "//sw/device/silicon_creator/lib:error",
            "//sw/device/silicon_creator/lib/drivers:retention_sram",
            "//sw/device/silicon_creator/lib/drivers:rstmgr",
        ],
    )
    for testcase in ALERT_INFO_TESTCASES
]
