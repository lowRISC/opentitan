# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load(
    "//rules:opentitan_test.bzl",
    "cw310_params",
    "opentitan_functest",
)
load(
    "//rules:const.bzl",
    "CONST",
    "EARLGREY_ALERTS",
    "EARLGREY_LOC_ALERTS",
    "get_lc_items",
    "hex",
)
load(
    "//rules:opentitan.bzl",
    "get_key_structs_for_lc_state",
    "opentitan_flash_binary",
)
load(
    "//rules:otp.bzl",
    "STD_OTP_OVERLAYS",
    "otp_alert_classification",
    "otp_alert_digest",
    "otp_hex",
    "otp_image",
    "otp_json",
    "otp_partition",
    "otp_per_class_bytes",
    "otp_per_class_ints",
    "otp_per_class_lists",
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

# Alert Handler configuration test cases.
#
# These test cases verify the ROM correctly configures the alert_handler in each
# life cycle state.

# Alert handler configuration is not checked in the TEST LC state.
ALERT_LC_STATES = get_lc_items(
    CONST.LCV.PROD,
    CONST.LCV.PROD_END,
    CONST.LCV.DEV,
    CONST.LCV.RMA,
)

[otp_image(
    name = "otp_img_alert_{}".format(lc_state),
    src = "//hw/ip/otp_ctrl/data:otp_json_{}".format(lc_state),
    overlays = STD_OTP_OVERLAYS,
) for lc_state, _ in ALERT_LC_STATES]

[bitstream_splice(
    name = "bitstream_alert_{}".format(lc_state),
    src = "//hw/bitstream/hyperdebug:rom_with_fake_keys",
    data = ":otp_img_alert_{}".format(lc_state),
    meminfo = "//hw/bitstream/hyperdebug:otp_mmi",
    tags = maybe_skip_in_ci(lc_state_val),
    update_usr_access = True,
) for lc_state, lc_state_val in ALERT_LC_STATES]

[opentitan_flash_binary(
    name = "rom_e2e_alert_config_test_{}".format(lc_state),
    testonly = True,
    srcs = ["rom_e2e_alert_config_test.c"],
    devices = [
        "fpga_cw310",
    ],
    local_defines = [
        "OTP_ALERT_DIGEST=OTP_CTRL_PARAM_OWNER_SW_CFG_ROM_ALERT_DIGEST_{}_OFFSET".format(lc_state.upper()),
    ],
    deps = [
        "//hw/ip/otp_ctrl/data:otp_ctrl_regs",
        "//sw/device/lib/testing/test_framework:ottf_ld_silicon_creator_slot_a",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/lib/drivers:alert",
        "//sw/device/silicon_creator/lib/drivers:lifecycle",
        "//sw/device/silicon_creator/lib/drivers:otp",
    ],
) for lc_state, _ in ALERT_LC_STATES]

[
    opentitan_functest(
        name = "alert_{}".format(
            lc_state,
        ),
        cw310 = cw310_params(
            bitstream = ":bitstream_alert_{}".format(lc_state),
            interface = "hyper310",
            tags = maybe_skip_in_ci(lc_state_val),
        ),
        key_struct = get_key_structs_for_lc_state(
            CONST.LCV.PROD,
            spx = None,
        )[0],
        ot_flash_binary = ":rom_e2e_alert_config_test_{}".format(lc_state),
        signed = True,
        targets = [
            "cw310_rom_with_fake_keys",
        ],
    )
    for lc_state, lc_state_val in ALERT_LC_STATES
]

test_suite(
    name = "rom_e2e_alert_config",
    tags = ["manual"],
    tests = [
        "alert_{}".format(lc_state)
        for lc_state, _ in ALERT_LC_STATES
    ],
)

otp_json(
    name = "shutdown_alert_owner_sw_cfg",
    partitions = [
        otp_partition(
            name = "OWNER_SW_CFG",
            items = {
                # Enable bootstrap.
                "OWNER_SW_CFG_ROM_BOOTSTRAP_DIS": otp_hex(CONST.HARDENED_FALSE),
                # Report errors without any redaction.
                "OWNER_SW_CFG_ROM_ERROR_REPORTING": otp_hex(CONST.SHUTDOWN.REDACT.NONE),
                # Enable class A alerts.
                "OWNER_SW_CFG_ROM_ALERT_CLASS_EN": otp_per_class_bytes(
                    A = CONST.ALERT.ENABLE,
                    B = CONST.ALERT.NONE,
                    C = CONST.ALERT.NONE,
                    D = CONST.ALERT.NONE,
                ),
                # Configure class A to escalate until phase 3 and disable other classes.
                "OWNER_SW_CFG_ROM_ALERT_ESCALATION": otp_per_class_bytes(
                    A = CONST.ALERT.ESC_PHASE_3,
                    B = CONST.ALERT.ESC_NONE,
                    C = CONST.ALERT.ESC_NONE,
                    D = CONST.ALERT.ESC_NONE,
                ),
                # Classify UART0 alerts (alert source 0) as class A and leave others as unconfigured.
                "OWNER_SW_CFG_ROM_ALERT_CLASSIFICATION": otp_alert_classification(
                    alert_list = EARLGREY_ALERTS,
                    # The ordering is "prod, prod_end, dev, rma"
                    default = "          X, X, X, X",
                    uart0_fatal_fault = "A, A, A, A",
                ),
                # Leave local alert classification as unconfigured.
                "OWNER_SW_CFG_ROM_LOCAL_ALERT_CLASSIFICATION": otp_alert_classification(
                    alert_list = EARLGREY_LOC_ALERTS,
                    default = "X, X, X, X",
                ),
                # Set the alert accumulation thresholds to 0.
                "OWNER_SW_CFG_ROM_ALERT_ACCUM_THRESH": otp_per_class_ints(
                    A = 0,
                    B = 0,
                    C = 0,
                    D = 0,
                ),
                # Set the alert timeout cycles to 0.
                "OWNER_SW_CFG_ROM_ALERT_TIMEOUT_CYCLES": otp_per_class_ints(
                    A = 0,
                    B = 0,
                    C = 0,
                    D = 0,
                ),
                # Set the alert phase cycles to 0.
                "OWNER_SW_CFG_ROM_ALERT_PHASE_CYCLES": otp_per_class_lists(
                    A = "0, 0, 0, 0",
                    B = "0, 0, 0, 0",
                    C = "0, 0, 0, 0",
                    D = "0, 0, 0, 0",
                ),
            },
        ),
    ],
)

otp_alert_digest(
    name = "shutdown_alert_digest_cfg",
    otp_img = ":shutdown_alert_owner_sw_cfg",
)

[otp_image(
    name = "otp_img_shutdown_alert_{}".format(lc_state),
    src = "//hw/ip/otp_ctrl/data:otp_json_{}".format(lc_state),
    overlays = STD_OTP_OVERLAYS + [
        ":shutdown_alert_owner_sw_cfg",
        ":shutdown_alert_digest_cfg",
    ],
) for lc_state, _ in ALERT_LC_STATES]

[bitstream_splice(
    name = "bitstream_shutdown_alert_{}".format(lc_state),
    src = "//hw/bitstream/hyperdebug:rom_with_fake_keys",
    data = ":otp_img_shutdown_alert_{}".format(lc_state),
    meminfo = "//hw/bitstream/hyperdebug:otp_mmi",
    tags = maybe_skip_in_ci(lc_state_val),
    update_usr_access = True,
) for lc_state, lc_state_val in ALERT_LC_STATES]

[opentitan_flash_binary(
    name = "rom_e2e_shutdown_alert_config_test_{}".format(lc_state),
    testonly = True,
    srcs = ["rom_e2e_shutdown_alert_config_test.c"],
    devices = [
        "fpga_cw310",
    ],
    deps = [
        "//hw/ip/uart/data:uart_regs",
        "//sw/device/lib/base:abs_mmio",
        "//sw/device/lib/testing/test_framework:ottf_ld_silicon_creator_slot_a",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/lib/drivers:retention_sram",
        "//sw/device/silicon_creator/lib/drivers:rstmgr",
    ],
) for lc_state, _ in ALERT_LC_STATES]

[
    opentitan_functest(
        name = "shutdown_alert_{}".format(lc_state),
        cw310 = cw310_params(
            bitstream = ":bitstream_shutdown_alert_{}".format(lc_state),
            interface = "hyper310",
            tags = maybe_skip_in_ci(lc_state_val),
        ),
        key_struct = get_key_structs_for_lc_state(
            CONST.LCV.PROD,
            spx = None,
        )[0],
        ot_flash_binary = ":rom_e2e_shutdown_alert_config_test_{}".format(lc_state),
        signed = True,
        targets = [
            "cw310_rom_with_fake_keys",
        ],
    )
    for lc_state, lc_state_val in ALERT_LC_STATES
]

test_suite(
    name = "rom_e2e_shutdown_alert_config",
    tags = ["manual"],
    tests = [
        "shutdown_alert_{}".format(lc_state)
        for lc_state, _ in ALERT_LC_STATES
    ],
)
