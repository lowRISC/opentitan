# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:autogen.bzl", "autogen_hjson_header")
load("//rules:otp.bzl", "otp_image", "otp_json", "otp_partition")
load("@rules_pkg//pkg:mappings.bzl", "pkg_files")

package(default_visibility = ["//visibility:public"])

# This package must be kept in sync with get_otp_images() from //rules:otp.bzl.
# That is, each OTP image referenced by the macro should have a definition in
# this BUILD file.

filegroup(
    name = "all_files",
    srcs = glob(["**"]),
)

autogen_hjson_header(
    name = "otp_ctrl_regs",
    srcs = [
        "otp_ctrl.hjson",
    ],
)

otp_json(
    name = "otp_json_creator_sw_cfg",
    partitions = [
        otp_partition(
            name = "CREATOR_SW_CFG",
            items = {
                "CREATOR_SW_CFG_DIGEST": "0x0",
                # Use software mod_exp implementation for signature
                # verification. See the definition of `hardened_bool_t` in
                # sw/device/lib/base/hardened.h.
                "CREATOR_SW_CFG_USE_SW_RSA_VERIFY": "0x739",
                # Mark the first two keys as valid and remaining as invalid
                # since we have currently only two keys. See the definition of
                # `hardened_byte_bool_t` in sw/device/lib/base/hardened.h.
                "CREATOR_SW_CFG_KEY_IS_VALID": "0x4b4b4b4b4b4ba5a5",
                # Enable use of entropy for countermeasures. See the definition
                # of `hardened_bool_t` in sw/device/lib/base/hardened.h.
                "CREATOR_SW_CFG_RNG_EN": "0x739",
                # ROM execution is enabled if this item is set to a non-zero
                # value.
                "CREATOR_SW_CFG_ROM_EXEC_EN": "0xffffffff",
                # Value to write to the cpuctrl CSR in `rom_init()`.
                # See:
                # https://ibex-core.readthedocs.io/en/latest/03_reference/cs_registers.html#cpu-control-register-cpuctrl
                "CREATOR_SW_CFG_CPUCTRL": "0x1",
                "CREATOR_SW_CFG_JITTER_EN": "0x9",
                # Value of the min_security_version_rom_ext field of the
                # default boot data.
                "CREATOR_SW_CFG_MIN_SEC_VER_ROM_EXT": "0x0",
                # Value of the min_security_version_bl0 field of the default
                # boot data.
                "CREATOR_SW_CFG_MIN_SEC_VER_BL0": "0x0",
                # Enable the default boot data in PROD and PROD_END life cycle
                # states. See the definition of `hardened_bool_t` in
                # sw/device/lib/base/hardened.h.
                "CREATOR_SW_CFG_DEFAULT_BOOT_DATA_IN_PROD_EN": "0x739",
            },
        ),
    ],
)

otp_json(
    name = "otp_json_owner_sw_cfg",
    partitions = [
        otp_partition(
            name = "OWNER_SW_CFG",
            items = {
                "OWNER_SW_CFG_DIGEST": "0x0",
                # Enable bootstrap. See `hardened_bool_t` in
                # sw/device/lib/base/hardened.h.
                "OWNER_SW_CFG_ROM_BOOTSTRAP_EN": "0x739",
                # Set to 0x739 to use the ROM_EXT hash measurement as the key
                # manager attestation binding value.
                "OWNER_SW_CFG_ROM_KEYMGR_ROM_EXT_MEAS_EN": "0x0",
                # Set the enables to kAlertEnableNone.
                # See `alert_enable_t` in
                # sw/device/silicon_creator/lib/drivers/alert.h
                "OWNER_SW_CFG_ROM_ALERT_CLASS_EN": "0xa9a9a9a9",
                # Set the esclation policies to kAlertEscalateNone.
                # See `alert_escalate_t` in
                # sw/device/silicon_creator/lib/drivers/alert.h
                "OWNER_SW_CFG_ROM_ALERT_ESCALATION": "0xd1d1d1d1",
                # Set the classifiactions to kAlertClassX.
                # See `alert_class_t` in
                # sw/device/silicon_creator/lib/drivers/alert.h
                "OWNER_SW_CFG_ROM_ALERT_CLASSIFICATION": ["0x94949494"] * 80,
                # Set the classifiactions to kAlertClassX. See `alert_class_t` in
                # sw/device/silicon_creator/lib/drivers/alert.h
                "OWNER_SW_CFG_ROM_LOCAL_ALERT_CLASSIFICATION": ["0x94949494"] * 16,
                # Set the alert accumulation thresholds to 0 per class.
                "OWNER_SW_CFG_ROM_ALERT_ACCUM_THRESH": ["0x00000000"] * 4,
                # Set the alert timeout cycles to 0 per class.
                "OWNER_SW_CFG_ROM_ALERT_TIMEOUT_CYCLES": ["0x00000000"] * 4,
                # Set the alert phase cycles to 0,10,10,0xFFFFFFFF for classes
                # A and B, and to all zeros for classes C and D.
                "OWNER_SW_CFG_ROM_ALERT_PHASE_CYCLES": [
                    "0x0",
                    "0xa",
                    "0xa",
                    "0xFFFFFFFF",
                    "0x0",
                    "0xa",
                    "0xa",
                    "0xFFFFFFFF",
                    "0x0",
                    "0x0",
                    "0x0",
                    "0x0",
                    "0x0",
                    "0x0",
                    "0x0",
                    "0x0",
                ],
                "OWNER_SW_CFG_ROM_ALERT_DIGEST_RMA": "0x36ed9cb0",
            },
        ),
    ],
)

otp_json(
    name = "otp_json_hw_cfg",
    partitions = [
        otp_partition(
            name = "HW_CFG",
            items = {
                "DEVICE_ID": "<random>",
                # Cryptolib and chip-level tests require access to the CSRNG
                # software interfaces.
                "EN_CSRNG_SW_APP_READ": True,
                # Cryptolib and chip-level tests require access to the
                # entropy_src FW data interface.
                "EN_ENTROPY_SRC_FW_READ": True,
                # Cryptolib and chip-level tests require access to the
                # entropy_src FW override interface.
                "EN_ENTROPY_SRC_FW_OVER": True,
            },
            lock = True,
        ),
    ],
)

# OTP LC STATE-SPECIFIC CONFIGS
otp_json(
    name = "otp_json_raw",
    partitions = [
        otp_partition(
            name = "SECRET1",
            items = {
                "FLASH_DATA_KEY_SEED": "<random>",
            },
            lock = False,
        ),
        otp_partition(
            name = "LIFE_CYCLE",
            count = 0,
            state = "RAW",
        ),
    ],
    seed = "01931961561863975174",
)

otp_json(
    name = "otp_json_test_unlocked0",
    partitions = [
        otp_partition(
            name = "CREATOR_SW_CFG",
            items = {
                # ROM execution is enabled if this item is set to a non-zero value.
                "CREATOR_SW_CFG_ROM_EXEC_EN": "0xffffffff",
            },
        ),
        otp_partition(
            name = "LIFE_CYCLE",
            count = 1,
            state = "TEST_UNLOCKED0",
        ),
    ],
    seed = "01931961561863975174",
)

otp_json(
    name = "otp_json_dev",
    partitions = [
        otp_partition(
            name = "SECRET0",
            items = {
                "TEST_UNLOCK_TOKEN": "<random>",
                "TEST_EXIT_TOKEN": "<random>",
            },
            lock = True,
        ),
        otp_partition(
            name = "SECRET1",
            items = {
                "FLASH_ADDR_KEY_SEED": "<random>",
                "FLASH_DATA_KEY_SEED": "<random>",
                "SRAM_DATA_KEY_SEED": "<random>",
            },
            lock = True,
        ),
        otp_partition(
            name = "SECRET2",
            items = {
                "RMA_TOKEN": "<random>",
                "CREATOR_ROOT_KEY_SHARE0": "<random>",
                "CREATOR_ROOT_KEY_SHARE1": "<random>",
            },
            lock = False,
        ),
        otp_partition(
            name = "LIFE_CYCLE",
            count = "5",
            state = "DEV",
        ),
    ],
    seed = "94259314771464387",
)

otp_json(
    name = "otp_json_prod",
    partitions = [
        otp_partition(
            name = "SECRET0",
            items = {
                "TEST_UNLOCK_TOKEN": "<random>",
                "TEST_EXIT_TOKEN": "<random>",
            },
            lock = True,
        ),
        otp_partition(
            name = "SECRET1",
            items = {
                "FLASH_ADDR_KEY_SEED": "<random>",
                "FLASH_DATA_KEY_SEED": "<random>",
                "SRAM_DATA_KEY_SEED": "<random>",
            },
            lock = True,
        ),
        otp_partition(
            name = "SECRET2",
            items = {
                "RMA_TOKEN": "<random>",
                "CREATOR_ROOT_KEY_SHARE0": "<random>",
                "CREATOR_ROOT_KEY_SHARE1": "<random>",
            },
            lock = False,
        ),
        otp_partition(
            name = "LIFE_CYCLE",
            count = 5,
            state = "PROD",
        ),
    ],
    seed = "14555711126514784208",
)

otp_json(
    name = "otp_json_rma",
    partitions = [
        otp_partition(
            name = "SECRET0",
            items = {
                "TEST_UNLOCK_TOKEN": "<random>",
                "TEST_EXIT_TOKEN": "<random>",
            },
            lock = True,
        ),
        otp_partition(
            name = "SECRET1",
            items = {
                "FLASH_ADDR_KEY_SEED": "<random>",
                "FLASH_DATA_KEY_SEED": "<random>",
                "SRAM_DATA_KEY_SEED": "<random>",
            },
            lock = True,
        ),
        otp_partition(
            name = "SECRET2",
            items = {
                "RMA_TOKEN": "<random>",
                "CREATOR_ROOT_KEY_SHARE0": "<random>",
                "CREATOR_ROOT_KEY_SHARE1": "<random>",
            },
            lock = False,
        ),
        otp_partition(
            name = "LIFE_CYCLE",
            count = 8,
            state = "RMA",
        ),
    ],
    seed = "01931961561863975174",
)

otp_image(
    name = "img_dev",
    src = ":otp_json_dev",
    overlays = [
        ":otp_json_creator_sw_cfg",
        ":otp_json_owner_sw_cfg",
        ":otp_json_hw_cfg",
    ],
)

otp_image(
    name = "img_prod",
    src = ":otp_json_prod",
    overlays = [
        ":otp_json_creator_sw_cfg",
        ":otp_json_owner_sw_cfg",
        ":otp_json_hw_cfg",
    ],
)

otp_image(
    name = "img_raw",
    src = ":otp_json_raw",
    overlays = [
        ":otp_json_creator_sw_cfg",
        ":otp_json_owner_sw_cfg",
        ":otp_json_hw_cfg",
    ],
)

otp_image(
    name = "img_rma",
    src = ":otp_json_rma",
    overlays = [
        ":otp_json_creator_sw_cfg",
        ":otp_json_owner_sw_cfg",
        ":otp_json_hw_cfg",
    ],
)

otp_image(
    name = "img_test_unlocked0",
    src = ":otp_json_test_unlocked0",
    overlays = [
        ":otp_json_creator_sw_cfg",
        ":otp_json_owner_sw_cfg",
        ":otp_json_hw_cfg",
    ],
)

# Create an execution-disabling overlay
otp_json(
    name = "otp_json_exec_disabled",
    partitions = [
        otp_partition(
            name = "CREATOR_SW_CFG",
            items = {"CREATOR_SW_CFG_ROM_EXEC_EN": "0x0"},
        ),
    ],
)

otp_image(
    name = "img_exec_disabled",
    src = ":otp_json_rma",
    overlays = [
        ":otp_json_creator_sw_cfg",
        ":otp_json_owner_sw_cfg",
        ":otp_json_hw_cfg",
        ":otp_json_exec_disabled",
    ],
)

filegroup(
    name = "otp_imgs",
    srcs = [
        ":img_dev",
        ":img_prod",
        ":img_raw",
        ":img_rma",
        ":img_test_unlocked0",
    ],
)

pkg_files(
    name = "package",
    srcs = [":otp_imgs"],
    prefix = "earlgrey/otp",
)
