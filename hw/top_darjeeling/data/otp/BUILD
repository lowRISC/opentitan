# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_pkg//pkg:mappings.bzl", "pkg_files")
load("//rules:const.bzl", "CONST", "DARJEELING_LOC_ALERTS")
load("//hw/top_darjeeling/data/autogen:defs.bzl", "DARJEELING_ALERTS")
load(
    "//rules:otp.bzl",
    "OTP_SIGVERIFY_FAKE_KEYS",
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
load("//hw/top:defs.bzl", "opentitan_require_top")

package(default_visibility = ["//visibility:public"])

# All otp_json targets are marked as compatible only with Darjeeling to avoid
# using them on other tops by mistake
TARGET_COMPATIBLE_WITH = opentitan_require_top("darjeeling")

exports_files(["otp_ctrl_mmap.hjson"])

otp_json(
    name = "otp_json_creator_sw_cfg",
    partitions = [
        otp_partition(
            name = "CREATOR_SW_CFG",
            items = {
                # Disable SPX+ signature verification. See the definition of
                # `kSigverifySpxDisabledOtp` in
                # sw/device/silicon_creator/lib/sigverify/spx_verify.h.
                "CREATOR_SW_CFG_SIGVERIFY_SPX_EN": otp_hex(0x8d6c8c17),
                # Enable use of entropy for countermeasures. See the definition
                # of `hardened_bool_t` in sw/device/lib/base/hardened.h.
                "CREATOR_SW_CFG_RNG_EN": otp_hex(CONST.HARDENED_TRUE),
                # Value to write to the cpuctrl CSR in `rom_init()`.
                # See:
                # https://ibex-core.readthedocs.io/en/latest/03_reference/cs_registers.html#cpu-control-register-cpuctrl
                "CREATOR_SW_CFG_CPUCTRL": otp_hex(0x1),
                "CREATOR_SW_CFG_JITTER_EN": otp_hex(CONST.MUBI4_FALSE),
            },
        ),
    ],
    target_compatible_with = TARGET_COMPATIBLE_WITH,
)

otp_json(
    name = "otp_json_owner_sw_cfg",
    partitions = [
        otp_partition(
            name = "OWNER_SW_CFG",
            items = {
                "OWNER_SW_CFG_ROM_ERROR_REPORTING": otp_hex(CONST.SHUTDOWN.REDACT.NONE),
                # Set the enables to kAlertEnableNone.
                # See `alert_enable_t` in
                # sw/device/silicon_creator/lib/drivers/alert.h
                "OWNER_SW_CFG_ROM_ALERT_CLASS_EN": otp_per_class_bytes(
                    A = CONST.ALERT.NONE,
                    B = CONST.ALERT.NONE,
                    C = CONST.ALERT.NONE,
                    D = CONST.ALERT.NONE,
                ),
                # Set the escalation policies to kAlertEscalateNone.
                # See `alert_escalate_t` in
                # sw/device/silicon_creator/lib/drivers/alert.h
                "OWNER_SW_CFG_ROM_ALERT_ESCALATION": otp_per_class_bytes(
                    A = CONST.ALERT.ESC_NONE,
                    B = CONST.ALERT.ESC_NONE,
                    C = CONST.ALERT.ESC_NONE,
                    D = CONST.ALERT.ESC_NONE,
                ),
                # Set the classifications to kAlertClassX.
                # See `alert_class_t` in
                # sw/device/silicon_creator/lib/drivers/alert.h
                "OWNER_SW_CFG_ROM_ALERT_CLASSIFICATION": otp_alert_classification(
                    alert_list = DARJEELING_ALERTS,
                    # The ordering is "prod, prod_end, dev, rma"
                    default = "X, X, X, X",
                ),

                # Set the classifications to kAlertClassX. See `alert_class_t` in
                # sw/device/silicon_creator/lib/drivers/alert.h
                "OWNER_SW_CFG_ROM_LOCAL_ALERT_CLASSIFICATION": otp_alert_classification(
                    alert_list = DARJEELING_LOC_ALERTS,
                    # The ordering is "prod, prod_end, dev, rma"
                    default = "X, X, X, X",
                ),
                # Set the alert accumulation thresholds to 0 per class.
                "OWNER_SW_CFG_ROM_ALERT_ACCUM_THRESH": otp_per_class_ints(
                    A = 0,
                    B = 0,
                    C = 0,
                    D = 0,
                ),
                # Set the alert timeout cycles to 0 per class.
                "OWNER_SW_CFG_ROM_ALERT_TIMEOUT_CYCLES": otp_per_class_ints(
                    A = 0,
                    B = 0,
                    C = 0,
                    D = 0,
                ),
                # Set the alert phase cycles to 0,10,10,0xFFFFFFFF for classes
                # A and B, and to all zeros for classes C and D.
                "OWNER_SW_CFG_ROM_ALERT_PHASE_CYCLES": otp_per_class_lists(
                    A = "0x0, 0xa, 0xa, 0xffffffff",
                    B = "0x0, 0xa, 0xa, 0xffffffff",
                    C = "0x0, 0x0, 0x0, 0x0",
                    D = "0x0, 0x0, 0x0, 0x0",
                ),
            },
        ),
    ],
    target_compatible_with = TARGET_COMPATIBLE_WITH,
)

otp_json(
    name = "otp_json_hw_cfg0",
    partitions = [
        otp_partition(
            name = "HW_CFG0",
            items = {
                "DEVICE_ID": "<random>",
            },
            lock = True,
        ),
    ],
    target_compatible_with = TARGET_COMPATIBLE_WITH,
)

otp_json(
    name = "otp_json_hw_cfg1",
    partitions = [
        otp_partition(
            name = "HW_CFG1",
            items = {
                # Enable code execution from SRAM.
                "EN_SRAM_IFETCH": True,
            },
            lock = True,
        ),
    ],
    target_compatible_with = TARGET_COMPATIBLE_WITH,
)

otp_json(
    name = "otp_json_hw_cfg2",
    partitions = [
        otp_partition(
            name = "HW_CFG2",
            items = {
                "SOC_DBG_STATE": "PROD",
            },
            lock = True,
        ),
    ],
    target_compatible_with = TARGET_COMPATIBLE_WITH,
)

otp_json(
    name = "otp_json_secret0",
    partitions = [
        otp_partition(
            name = "SECRET0",
            items = {
                "TEST_UNLOCK_TOKEN": "<random>",
                "TEST_EXIT_TOKEN": "<random>",
            },
            lock = True,
        ),
    ],
    target_compatible_with = TARGET_COMPATIBLE_WITH,
)

otp_json(
    name = "otp_json_secret1",
    partitions = [
        otp_partition(
            name = "SECRET1",
            items = {
                "SRAM_DATA_KEY_SEED": "<random>",
            },
            lock = True,
        ),
    ],
    target_compatible_with = TARGET_COMPATIBLE_WITH,
)

otp_json(
    name = "otp_json_secret2",
    partitions = [
        otp_partition(
            name = "SECRET2",
            items = {
                "RMA_TOKEN": "<random>",
                "CREATOR_ROOT_KEY_SHARE0": "<random>",
                "CREATOR_ROOT_KEY_SHARE1": "<random>",
                "CREATOR_SEED": "<random>",
            },
            lock = True,
        ),
    ],
    target_compatible_with = TARGET_COMPATIBLE_WITH,
)

otp_json(
    name = "otp_json_secret2_unlocked",
    partitions = [
        otp_partition(
            name = "SECRET2",
            items = {
                "RMA_TOKEN": "<random>",
                "CREATOR_ROOT_KEY_SHARE0": "<random>",
                "CREATOR_ROOT_KEY_SHARE1": "<random>",
                "CREATOR_SEED": "<random>",
            },
            lock = False,
        ),
    ],
)

otp_json(
    name = "otp_json_soc_dbg_raw",
    partitions = [
        otp_partition(
            name = "HW_CFG1",
            items = {
                "EN_SRAM_IFETCH": True,
            },
            lock = True,
        ),
        otp_partition(
            name = "HW_CFG2",
            items = {
                "SOC_DBG_STATE": "BLANK",
            },
            lock = True,
        ),
    ],
    target_compatible_with = TARGET_COMPATIBLE_WITH,
)

otp_json(
    name = "otp_json_soc_dbg_pre_prod",
    partitions = [
        otp_partition(
            name = "HW_CFG1",
            items = {
                "EN_SRAM_IFETCH": True,
            },
            lock = True,
        ),
        otp_partition(
            name = "HW_CFG2",
            items = {
                "SOC_DBG_STATE": "PRE_PROD",
            },
            lock = True,
        ),
    ],
    target_compatible_with = TARGET_COMPATIBLE_WITH,
)

otp_json(
    name = "otp_json_soc_dbg_prod",
    partitions = [
        otp_partition(
            name = "HW_CFG1",
            items = {
                "EN_SRAM_IFETCH": True,
            },
            lock = True,
        ),
        otp_partition(
            name = "HW_CFG2",
            items = {
                "SOC_DBG_STATE": "PROD",
            },
            lock = True,
        ),
    ],
    target_compatible_with = TARGET_COMPATIBLE_WITH,
)

# OTP LC STATE-SPECIFIC CONFIGS
otp_json(
    name = "otp_json_raw",
    partitions = [
        otp_partition(
            name = "LIFE_CYCLE",
            count = 0,
            state = "RAW",
        ),
    ],
    target_compatible_with = TARGET_COMPATIBLE_WITH,
)

[
    otp_json(
        name = "otp_json_test_unlocked{}".format(i),
        partitions = [
            otp_partition(
                name = "LIFE_CYCLE",
                count = (i * 2) + 1,
                state = "TEST_UNLOCKED{}".format(i),
            ),
        ],
        target_compatible_with = TARGET_COMPATIBLE_WITH,
    )
    for i in range(0, 8)
]

[
    otp_json(
        name = "otp_json_test_locked{}".format(i),
        partitions = [
            otp_partition(
                name = "LIFE_CYCLE",
                count = (i + 1) * 2,
                state = "TEST_LOCKED{}".format(i),
            ),
        ],
        target_compatible_with = TARGET_COMPATIBLE_WITH,
    )
    for i in range(0, 7)
]

otp_json(
    name = "otp_json_dev",
    partitions = [
        otp_partition(
            name = "LIFE_CYCLE",
            count = "5",
            state = "DEV",
        ),
    ],
    target_compatible_with = TARGET_COMPATIBLE_WITH,
)

otp_json(
    name = "otp_json_prod",
    partitions = [
        otp_partition(
            name = "LIFE_CYCLE",
            count = 5,
            state = "PROD",
        ),
    ],
    target_compatible_with = TARGET_COMPATIBLE_WITH,
)

otp_json(
    name = "otp_json_prod_end",
    partitions = [
        otp_partition(
            name = "LIFE_CYCLE",
            count = 5,
            state = "PROD_END",
        ),
    ],
    target_compatible_with = TARGET_COMPATIBLE_WITH,
)

otp_json(
    name = "otp_json_rma",
    partitions = [
        otp_partition(
            name = "LIFE_CYCLE",
            count = 8,
            state = "RMA",
        ),
    ],
    target_compatible_with = TARGET_COMPATIBLE_WITH,
)

# Create an overlay for the alert_handler digest.
otp_alert_digest(
    name = "otp_json_alert_digest_cfg",
    otp_img = ":otp_json_owner_sw_cfg",
)

# The RAW OTP image only contains the LIFE_CYCLE partition, which is set to RAW
# state. All other partitions are left with default values to ensure the state
# of OTP is representative of post-silicon scenarios.
otp_image(
    name = "img_raw",
    src = ":otp_json_raw",
)

[
    # TEST_UNLOCKED images are expected to only have the SECRET0 partition
    # configured, as well as ROM execution enabled in the CREATOR_SW partition.
    # All other partitions are left with default values to ensure the state of
    # OTP is representative of post-silicon scenarios.
    otp_image(
        name = "img_test_unlocked{}".format(i),
        src = ":otp_json_test_unlocked{}".format(i),
        overlays = [
            ":otp_json_secret0",
            ":otp_json_creator_sw_cfg",
        ],
        target_compatible_with = TARGET_COMPATIBLE_WITH,
    )
    for i in range(0, 8)
]

[
    otp_image(
        name = "img_test_locked{}".format(i),
        src = ":otp_json_test_locked{}".format(i),
        overlays = [
            ":otp_json_secret0",
            ":otp_json_creator_sw_cfg",
        ],
        target_compatible_with = TARGET_COMPATIBLE_WITH,
    )
    for i in range(0, 7)
]

otp_image(
    name = "img_dev",
    src = ":otp_json_dev",
    overlays = STD_OTP_OVERLAYS,
)

otp_image(
    name = "img_prod",
    src = ":otp_json_prod",
    overlays = STD_OTP_OVERLAYS,
)

otp_image(
    name = "img_prod_end",
    src = ":otp_json_prod_end",
    overlays = STD_OTP_OVERLAYS,
)

otp_image(
    name = "img_rma",
    src = ":otp_json_rma",
    overlays = STD_OTP_OVERLAYS,
)

filegroup(
    name = "otp_imgs",
    srcs = [
        ":img_dev",
        ":img_prod",
        ":img_raw",
        ":img_rma",
        ":img_test_locked0",
        ":img_test_locked1",
        ":img_test_locked2",
        ":img_test_locked3",
        ":img_test_locked4",
        ":img_test_locked5",
        ":img_test_locked6",
        ":img_test_unlocked0",
        ":img_test_unlocked1",
        ":img_test_unlocked2",
        ":img_test_unlocked3",
        ":img_test_unlocked4",
        ":img_test_unlocked5",
        ":img_test_unlocked6",
        ":img_test_unlocked7",
    ],
)

pkg_files(
    name = "package",
    srcs = [":otp_imgs"],
    prefix = "darjeeling/otp",
)

# Partition used to set a fixed seed value in `otp_image_consts` targets.
otp_json(
    name = "otp_json_baseline",
)
