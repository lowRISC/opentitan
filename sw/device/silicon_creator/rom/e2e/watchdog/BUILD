# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load(
    "//rules:opentitan_test.bzl",
    "cw310_params",
    "opentitan_functest",
    "verilator_params",
)
load(
    "//rules:const.bzl",
    "get_lc_items",
)
load(
    "//rules:opentitan.bzl",
    "get_key_structs_for_lc_state",
    "opentitan_flash_binary",
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
load(
    "//rules:splice.bzl",
    "bitstream_splice",
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
[otp_image(
    name = "otp_img_watchdog_enable_{}".format(lc_state),
    src = "//hw/ip/otp_ctrl/data:otp_json_{}".format(lc_state),
    overlays = STD_OTP_OVERLAYS + [":otp_json_watchdog_enable"],
) for lc_state, _ in get_lc_items()]

# Bitstreams with the watchdog-enable OTP images spliced in.
[bitstream_splice(
    name = "bitstream_watchdog_enable_{}".format(lc_state),
    src = "//hw/bitstream:rom_with_fake_keys",
    data = ":otp_img_watchdog_enable_{}".format(lc_state),
    meminfo = "//hw/bitstream:otp_mmi",
    tags = maybe_skip_in_ci(lc_state_val),
    update_usr_access = True,
) for lc_state, lc_state_val in get_lc_items()]

# Creates a binary that confirms the watchdog is enabled and a binary that
# confirms the watchdog is disabled.
[opentitan_flash_binary(
    name = "test_watchdog_{}".format(watchdog_config),
    testonly = True,
    srcs = ["watchdog_test.c"],
    devices = [
        "fpga_cw310",
        "sim_verilator",
    ],
    local_defines = [
        "EXPECT_WATCHDOG_{}".format(watchdog_config.upper()),
        "WATCHDOG_BITE_THRESHOLD={}".format(WATCHDOG_BITE_THRESHOLD),
    ],
    deps = [
        "//hw/ip/aon_timer/data:aon_timer_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:abs_mmio",
        "//sw/device/lib/testing/test_framework:ottf_ld_silicon_creator_slot_a",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
) for watchdog_config in [
    "disabled",
    "enabled",
]]

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

# Bitstream targets (CW310) and otp images (verilator) for the watchdog config
# tests. The format argument should be replaced with the desired life cycle
# state.
WATCHDOG_BITSTREAM = {
    "disable": "//hw/bitstream:rom_with_fake_keys_otp_{}",
    "enable": ":bitstream_watchdog_enable_{}",
}

WATCHDOG_OTP = {
    "disable": "//hw/ip/otp_ctrl/data:img_{}",
    "enable": ":otp_img_watchdog_enable_{}",
}

[
    opentitan_functest(
        name = "watchdog_{}_{}".format(
            otp_config,
            lc_state,
        ),
        cw310 = cw310_params(
            bitstream = WATCHDOG_BITSTREAM[otp_config].format(lc_state),
            tags = maybe_skip_in_ci(lc_state_val),
        ),
        key_struct = get_key_structs_for_lc_state(
            lc_state_val,
            spx = None,
        )[0],
        ot_flash_binary = ":test_watchdog_{}".format(WATCHDOG_TEST_CASES[otp_config][lc_state]),
        signed = True,
        targets = [
            "cw310_rom_with_fake_keys",
            "verilator",
        ],
        verilator = verilator_params(
            timeout = "eternal",
            otp = WATCHDOG_OTP[otp_config].format(lc_state),
            rom = "//sw/device/silicon_creator/rom:rom_with_fake_keys",
            # Test cases that enable the watchdog time out in verilator, cause
            # unknown.
            tags = ["broken"] if WATCHDOG_TEST_CASES[otp_config][lc_state] == "enabled" else [],
        ),
    )
    for otp_config in [
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
