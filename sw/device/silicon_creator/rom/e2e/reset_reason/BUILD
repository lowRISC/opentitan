# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load(
    "//rules/opentitan:defs.bzl",
    "DEFAULT_TEST_FAILURE_MSG",
    "DEFAULT_TEST_SUCCESS_MSG",
    "fpga_params",
    "opentitan_test",
)
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
    name = "otp_json_reset_reason",
    partitions = [
        otp_partition(
            name = "OWNER_SW_CFG",
            items = {
                "OWNER_SW_CFG_ROM_PRESERVE_RESET_REASON_EN": otp_hex(CONST.HARDENED_TRUE),
            },
        ),
    ],
)

# OTP images that enable the watchdog.
otp_image(
    name = "otp_img_reset_reason",
    src = "//hw/ip/otp_ctrl/data:otp_json_rma",
    overlays = STD_OTP_OVERLAYS + [":otp_json_reset_reason"],
)

opentitan_test(
    name = "reset_reasons_test",
    srcs = ["reset_reasons_test.c"],
    exec_env = {
        "//hw/top_earlgrey:fpga_cw310_rom_with_fake_keys": None,
        "//hw/top_earlgrey:fpga_cw340_rom_with_fake_keys": None,
    },
    fpga = fpga_params(
        otp = ":otp_img_reset_reason",
    ),
    deps = [
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/lib/drivers:rstmgr",
    ],
)

RESET_CORRUPTION_SCENARIOS = [
    {
        "name": "check_uninitialized",
        # This is effectively the same as "check_enabled_no_fault" because
        # the upper and lower half-words have the same value and the value
        # isn't HARDENED_FALSE.
        "otp": 0,
        "exit_success": DEFAULT_TEST_SUCCESS_MSG,
        "exit_failure": DEFAULT_TEST_FAILURE_MSG,
        "test_cmd": "",
    },
    {
        "name": "check_disabled_no_fault",
        "otp": CONST.HARDENED_FALSE << 16 | CONST.HARDENED_FALSE,
        "exit_success": DEFAULT_TEST_SUCCESS_MSG,
        "exit_failure": DEFAULT_TEST_FAILURE_MSG,
        "test_cmd": "",
    },
    {
        "name": "check_disabled_with_fault",
        # Setting the check half-word to any value different from the enable
        # half-word guarantees a fault-detection in the ROM regardless of what
        # is actually read from the reset reason register.
        "otp": CONST.HARDENED_FALSE << 16 | 0,
        "exit_success": DEFAULT_TEST_SUCCESS_MSG,
        "exit_failure": DEFAULT_TEST_FAILURE_MSG,
        "test_cmd": "",
    },
    {
        "name": "check_enabled_no_fault",
        "otp": CONST.HARDENED_TRUE << 16 | CONST.HARDENED_TRUE,
        "exit_success": DEFAULT_TEST_SUCCESS_MSG,
        "exit_failure": DEFAULT_TEST_FAILURE_MSG,
        "test_cmd": "",
    },
    {
        "name": "check_enabled_with_fault",
        # Setting the check half-word to any value different from the enable
        # half-word guarantees a fault-detection in the ROM regardless of what
        # is actually read from the reset reason register.
        "otp": CONST.HARDENED_TRUE << 16 | 0,
        # This is the specific fault code of a reset reason corruption.
        "exit_success": "BFV:024d5202\r\n",
        "exit_failure": DEFAULT_TEST_SUCCESS_MSG,
        # This test will fault before bootstrap straps are read, so simply
        # start the console and look for the fault message.
        "test_cmd": """
            --exec="transport init"
            --exec="fpga load-bitstream {bitstream}"
            --exec="console --non-interactive --exit-success='{exit_success}' --exit-failure='{exit_failure}'"
            no-op
        """,
    },
]

[
    otp_json(
        name = "otp_json_reset_reason_{}".format(t["name"]),
        partitions = [
            otp_partition(
                name = "OWNER_SW_CFG",
                items = {
                    "OWNER_SW_CFG_ROM_RESET_REASON_CHECK_VALUE": otp_hex(t["otp"]),
                },
            ),
        ],
    )
    for t in RESET_CORRUPTION_SCENARIOS
]

[
    otp_image(
        name = "otp_img_reset_reason_{}".format(t["name"]),
        src = "//hw/ip/otp_ctrl/data:otp_json_rma",
        overlays = STD_OTP_OVERLAYS + [
            ":otp_json_reset_reason_{}".format(t["name"]),
        ],
    )
    for t in RESET_CORRUPTION_SCENARIOS
]

[
    opentitan_test(
        name = "reset_reason_{}".format(t["name"]),
        srcs = ["//sw/device/silicon_creator/rom/e2e:empty_test"],
        exec_env = {
            "//hw/top_earlgrey:fpga_cw310_rom_with_fake_keys": None,
            "//hw/top_earlgrey:fpga_cw340_rom_with_fake_keys": None,
        },
        fpga = fpga_params(
            exit_failure = t["exit_failure"],
            exit_success = t["exit_success"],
            otp = ":otp_img_reset_reason_{}".format(t["name"]),
            test_cmd = t["test_cmd"],
        ),
        deps = [
            "//sw/device/lib/testing/test_framework:ottf_main",
        ],
    )
    for t in RESET_CORRUPTION_SCENARIOS
]

test_suite(
    name = "reset_reason_check",
    tags = ["manual"],
    tests = [
        ":reset_reason_{}".format(t["name"])
        for t in RESET_CORRUPTION_SCENARIOS
    ],
)
