# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load(
    "//rules/opentitan:defs.bzl",
    "cw310_params",
    "hyper310_params",
    "opentitan_test",
)
load(
    "//rules:const.bzl",
    "CONST",
    "error_redact",
    "get_lc_items",
    "hex_digits",
)
load(
    "//rules:otp.bzl",
    "STD_OTP_OVERLAYS",
    "otp_hex",
    "otp_image",
    "otp_json",
    "otp_partition",
)
load(
    "//rules:rom_e2e.bzl",
    "maybe_skip_in_ci",
)
load(
    "@bazel_skylib//lib:structs.bzl",
    "structs",
)
load(
    "//sw/device/silicon_creator/rom/e2e:defs.bzl",
    "MSG_PASS",
    "MSG_TEMPLATE_BFV",
)

package(default_visibility = ["//visibility:public"])

# Shutdown Redact Test

# Dict that also includes an invalid redaction value for test purposes.
REDACT = structs.to_dict(CONST.SHUTDOWN.REDACT)

REDACT.update({"INVALID": 0x0})

[
    otp_json(
        name = "otp_json_{}_overlay".format(k.lower()),
        partitions = [
            otp_partition(
                name = "OWNER_SW_CFG",
                items = {
                    "OWNER_SW_CFG_ROM_ERROR_REPORTING": otp_hex(v),
                },
            ),
        ],
    )
    for k, v in REDACT.items()
]

[
    otp_image(
        name = "img_{}_{}".format(
            lc_state,
            redact.lower(),
        ),
        src = "//hw/ip/otp_ctrl/data:otp_json_{}".format(lc_state),
        overlays = STD_OTP_OVERLAYS + [":otp_json_{}_overlay".format(redact.lower())],
        visibility = ["//visibility:private"],
    )
    for lc_state, _ in get_lc_items()
    for redact in REDACT
]

[
    opentitan_test(
        name = "e2e_shutdown_redact_{}_{}".format(
            lc_state,
            redact.lower(),
        ),
        cw310 = cw310_params(
            binaries = {
                "//sw/device/silicon_creator/rom/e2e:new_empty_test_slot_a": "firmware",
            },
            exit_failure = MSG_PASS,
            exit_success = MSG_TEMPLATE_BFV.format(hex_digits(error_redact(
                CONST.BFV.BOOT_POLICY.BAD_IDENTIFIER,
                lc_state_val,
                redact_val,
            ))),
            otp = ":img_{}_{}".format(
                lc_state,
                redact.lower(),
            ),
            tags = maybe_skip_in_ci(lc_state_val),
        ),
        exec_env = {
            "//hw/top_earlgrey:fpga_cw310_rom_with_fake_keys": None,
            "//hw/top_earlgrey:fpga_hyper310_rom_with_fake_keys": None,
        },
        hyper310 = hyper310_params(
            binaries = {
                "//sw/device/silicon_creator/rom/e2e:new_empty_test_slot_a": "firmware",
            },
            exit_failure = MSG_PASS,
            exit_success = MSG_TEMPLATE_BFV.format(hex_digits(error_redact(
                CONST.BFV.BOOT_POLICY.BAD_IDENTIFIER,
                lc_state_val,
                redact_val,
            ))),
            otp = ":img_{}_{}".format(
                lc_state,
                redact.lower(),
            ),
            tags = maybe_skip_in_ci(lc_state_val),
        ),
        # Skip signing by clearing the manifest configuration.
        manifest = None,
    )
    for lc_state, lc_state_val in get_lc_items()
    for redact, redact_val in REDACT.items()
]

test_suite(
    name = "rom_e2e_shutdown_redact",
    tags = ["manual"],
    tests = [
        "e2e_shutdown_redact_{}_{}".format(
            lc_state,
            redact.lower(),
        )
        for lc_state, _ in get_lc_items()
        for redact in REDACT
    ],
)
