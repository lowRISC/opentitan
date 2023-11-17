# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load(
    "//rules/opentitan:defs.bzl",
    "cw310_params",
    "hyper310_params",
    "opentitan_binary",
    "opentitan_test",
    "rsa_key_for_lc_state",
    "verilator_params",
)
load(
    "@//rules:opentitan.bzl",
    "RSA_ONLY_KEY_STRUCTS",
)
load(
    "//rules:const.bzl",
    "get_lc_items",
)
load(
    "//rules:otp.bzl",
    "STD_OTP_OVERLAYS",
    "otp_image",
    "otp_json",
    "otp_partition",
)
load(
    "//rules:rom_e2e.bzl",
    "maybe_skip_in_ci",
)

package(default_visibility = ["//visibility:public"])

# Watchdog configuration test cases.
#
# These test cases verify the ROM correctly configures the watchdog in each life
# cycle state. Tests are run for OTP configurations that disable the watchdog
# and for OTP configurations that enable the watchdog.

# Watchdog bite threshold for the watchdog-enabled cases. This is 2 seconds,
# assuming a 200kHz clock.
WATCHDOG_BITE_THRESHOLD = "0x61a80"

# OTP overlay that enables the watchdog. The bite threshold is 2 seconds,
# assuming a 200kHz clock.
otp_json(
    name = "otp_json_watchdog_enable",
    partitions = [
        otp_partition(
            name = "OWNER_SW_CFG",
            items = {"OWNER_SW_CFG_ROM_WATCHDOG_BITE_THRESHOLD_CYCLES": WATCHDOG_BITE_THRESHOLD},
        ),
    ],
)

# OTP images that enable the watchdog.
[
    otp_image(
        name = "otp_img_watchdog_enable_{}".format(lc_state),
        src = "//hw/ip/otp_ctrl/data:otp_json_{}".format(lc_state),
        overlays = STD_OTP_OVERLAYS + [":otp_json_watchdog_enable"],
    )
    for lc_state, _ in get_lc_items()
]

WATCHDOG_TEST_CASES = {
    "disable": {
        "dev": "disabled",
        "prod": "disabled",
        "prod_end": "disabled",
        "rma": "disabled",
        "test_unlocked0": "disabled",
    },
    "enable": {
        "dev": "enabled",
        "prod": "enabled",
        "prod_end": "enabled",
        "rma": "disabled",
        "test_unlocked0": "disabled",
    },
}

# Creates a binary that confirms the watchdog is enabled and a binary that
# confirms the watchdog is disabled.
[
    opentitan_binary(
        name = "test_watchdog_{}_{}".format(watchdog_config, lc_state),
        testonly = True,
        srcs = ["watchdog_test.c"],
        exec_env = [
            "//hw/top_earlgrey:fpga_cw310",
            "//hw/top_earlgrey:sim_verilator",
        ],
        local_defines = [
            "EXPECT_WATCHDOG_{}".format(watchdog_config.upper()),
            "WATCHDOG_BITE_THRESHOLD={}".format(WATCHDOG_BITE_THRESHOLD),
        ],
        manifest = "//sw/device/silicon_creator/rom_ext:manifest_standard",
        rsa_key = rsa_key_for_lc_state(
            RSA_ONLY_KEY_STRUCTS,
            lc_state_val,
        ),
        deps = [
            "//hw/ip/aon_timer/data:aon_timer_regs",
            "//hw/top_earlgrey/sw/autogen:top_earlgrey",
            "//sw/device/lib/base:abs_mmio",
            "//sw/device/lib/testing/test_framework:ottf_ld_silicon_creator_slot_a",
            "//sw/device/lib/testing/test_framework:ottf_main",
        ],
    )
    for watchdog_config in [
        "disabled",
        "enabled",
    ]
    for lc_state, lc_state_val in get_lc_items()
]

WATCHDOG_OTP = {
    "disable": "//hw/ip/otp_ctrl/data:img_{}",
    "enable": ":otp_img_watchdog_enable_{}",
}

[
    opentitan_test(
        name = "watchdog_{}_{}".format(
            watchdog_config,
            lc_state,
        ),
        cw310 = cw310_params(
            binaries = {
                ":test_watchdog_{}_{}".format(
                    WATCHDOG_TEST_CASES[watchdog_config][lc_state],
                    lc_state,
                ): "firmware",
            },
            otp = WATCHDOG_OTP[watchdog_config].format(lc_state),
            tags = maybe_skip_in_ci(lc_state_val),
        ),
        exec_env = {
            "@//hw/top_earlgrey:fpga_cw310_rom_with_fake_keys": None,
            "@//hw/top_earlgrey:fpga_hyper310_rom_with_fake_keys": None,
            "@//hw/top_earlgrey:sim_verilator": None,
        },
        hyper310 = hyper310_params(
            binaries = {
                ":test_watchdog_{}_{}".format(
                    WATCHDOG_TEST_CASES[watchdog_config][lc_state],
                    lc_state,
                ): "firmware",
            },
            otp = WATCHDOG_OTP[watchdog_config].format(lc_state),
            tags = maybe_skip_in_ci(lc_state_val),
        ),
        verilator = verilator_params(
            timeout = "eternal",
            binaries = {
                ":test_watchdog_{}_{}".format(
                    WATCHDOG_TEST_CASES[watchdog_config][lc_state],
                    lc_state,
                ): "firmware",
            },
            otp = WATCHDOG_OTP[watchdog_config].format(lc_state),
            rom = "//sw/device/silicon_creator/rom:rom_with_fake_keys",
            # Test cases that enable the watchdog time out in verilator, cause
            # unknown.
            tags = ["broken"] if WATCHDOG_TEST_CASES[watchdog_config][lc_state] == "enabled" else [],
        ),
    )
    for watchdog_config in [
        "disable",
        "enable",
    ]
    for lc_state, lc_state_val in get_lc_items()
]

test_suite(
    name = "rom_e2e_watchdog_reconfig",
    tags = ["manual"],
    tests = [
        "watchdog_{}_{}".format(
            otp_config,
            lc_state,
        )
        for otp_config in [
            "disable",
            "enable",
        ]
        for lc_state, _ in get_lc_items()
    ],
)
