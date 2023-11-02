# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load(
    "//rules:otp.bzl",
    "otp_alert_classification",
    "otp_alert_digest",
    "otp_bytestring",
    "otp_hex",
    "otp_image_consts",
    "otp_json",
    "otp_partition",
    "otp_per_class_bytes",
    "otp_per_class_ints",
    "otp_per_class_lists",
)
load("//rules:const.bzl", "CONST", "EARLGREY_ALERTS", "EARLGREY_LOC_ALERTS")

package(default_visibility = ["//visibility:public"])

# Dummy partition used in `otp_image_consts` targets.
otp_json(
    name = "otp_json_baseline",
    seed = "85452983286950371191603618368782861611109037138182535346147818831008789508651",
)

# Create an overlay for the alert_handler digest.
otp_alert_digest(
    name = "alert_digest_cfg",
    otp_img = ":otp_json_owner_sw_cfg",
)

# OTP SW Configuration for Test SKU.
otp_image_consts(
    name = "otp_sw_cfg_c_file",
    src = ":otp_json_baseline",
    overlays = [
        ":alert_digest_cfg",
        ":otp_json_creator_sw_cfg",
        ":otp_json_owner_sw_cfg",
    ],
)

cc_library(
    name = "otp_sw_cfg",
    srcs = [":otp_sw_cfg_c_file"],
    deps = [
        "//hw/ip/otp_ctrl/data:otp_ctrl_regs",
        "//sw/device/silicon_creator/manuf/lib:otp_img_types",
    ],
)

otp_json(
    name = "otp_json_creator_sw_cfg",
    partitions = [
        otp_partition(
            name = "CREATOR_SW_CFG",
            items = {
                # Use software mod_exp implementation for signature
                # verification. See the definition of `hardened_bool_t` in
                # sw/device/lib/base/hardened.h.
                "CREATOR_SW_CFG_SIGVERIFY_RSA_MOD_EXP_IBEX_EN": otp_hex(CONST.HARDENED_TRUE),
                # Mark the first 7 keys as valid and remaining as invalid since
                # we currently have only 7 keys. See the definition of
                # `hardened_byte_bool_t` in sw/device/lib/base/hardened.h.
                "CREATOR_SW_CFG_SIGVERIFY_RSA_KEY_EN": otp_bytestring([
                    CONST.HARDENED_BYTE_TRUE,  # key0
                    CONST.HARDENED_BYTE_TRUE,  # key1
                    CONST.HARDENED_BYTE_TRUE,  # key2
                    CONST.HARDENED_BYTE_TRUE,  # key3
                    CONST.HARDENED_BYTE_TRUE,  # key4
                    CONST.HARDENED_BYTE_TRUE,  # key5
                    CONST.HARDENED_BYTE_TRUE,  # key6
                    CONST.HARDENED_BYTE_FALSE,  # key7
                ]),
                # Disable SPX+ signature verification. See the definitions of
                # `kSigverifySpxDisabledOtp` and `kSigverifySpxEnabledOtp` in
                # sw/device/silicon_creator/lib/sigverify/spx_verify.h.
                "CREATOR_SW_CFG_SIGVERIFY_SPX_EN": otp_hex(0x8d6c8c17),
                # Enable flash data page scrambling and ECC.
                "CREATOR_SW_CFG_FLASH_DATA_DEFAULT_CFG": "0000090606",
                # Enable use of entropy for countermeasures. See the definition
                # of `hardened_bool_t` in sw/device/lib/base/hardened.h.
                "CREATOR_SW_CFG_RNG_EN": otp_hex(CONST.HARDENED_TRUE),
                # ROM execution is enabled if this item is set to a non-zero
                # value.
                "CREATOR_SW_CFG_ROM_EXEC_EN": otp_hex(0xffffffff),
                # Value to write to the cpuctrl CSR in `rom_init()`.
                # See:
                # https://ibex-core.readthedocs.io/en/latest/03_reference/cs_registers.html#cpu-control-register-cpuctrl
                "CREATOR_SW_CFG_CPUCTRL": otp_hex(0x1),
                "CREATOR_SW_CFG_JITTER_EN": otp_hex(CONST.MUBI4_FALSE),
                # Value of the min_security_version_rom_ext field of the
                # default boot data.
                "CREATOR_SW_CFG_MIN_SEC_VER_ROM_EXT": otp_hex(0x0),
                # Value of the min_security_version_bl0 field of the default
                # boot data.
                "CREATOR_SW_CFG_MIN_SEC_VER_BL0": otp_hex(0x0),
                # Enable the default boot data in PROD and PROD_END life cycle
                # states. See the definition of `hardened_bool_t` in
                # sw/device/lib/base/hardened.h.
                "CREATOR_SW_CFG_DEFAULT_BOOT_DATA_IN_PROD_EN": otp_hex(CONST.HARDENED_TRUE),
                # Enable AST initialization.
                "CREATOR_SW_CFG_AST_INIT_EN": otp_hex(CONST.MUBI4_TRUE),
                # TODO: This enables a busyloop in the ROM to give time to
                # trigger an RMA lifecycle transition via JTAG.  The current
                # value of 10 cycles is useful for test code which verifies
                # the path through the ROM.  This value is not useful for a
                # real chip.
                "CREATOR_SW_CFG_RMA_SPIN_EN": otp_hex(CONST.HARDENED_TRUE),
                "CREATOR_SW_CFG_RMA_SPIN_CYCLES": "10",
                # Entropy source health check default values. This needs to be
                # populated when `CREATOR_SW_CFG_RNG_EN` is set to true.
                "CREATOR_SW_CFG_RNG_REPCNT_THRESHOLDS": otp_hex(0xffffffff),
                "CREATOR_SW_CFG_RNG_REPCNTS_THRESHOLDS": otp_hex(0xffffffff),
                "CREATOR_SW_CFG_RNG_ADAPTP_HI_THRESHOLDS": otp_hex(0xffffffff),
                "CREATOR_SW_CFG_RNG_ADAPTP_LO_THRESHOLDS": otp_hex(0x0),
                "CREATOR_SW_CFG_RNG_BUCKET_THRESHOLDS": otp_hex(0xffffffff),
                "CREATOR_SW_CFG_RNG_MARKOV_HI_THRESHOLDS": otp_hex(0xffffffff),
                "CREATOR_SW_CFG_RNG_MARKOV_LO_THRESHOLDS": otp_hex(0x0),
                "CREATOR_SW_CFG_RNG_EXTHT_HI_THRESHOLDS": otp_hex(0xffffffff),
                "CREATOR_SW_CFG_RNG_EXTHT_LO_THRESHOLDS": otp_hex(0x0),
                "CREATOR_SW_CFG_RNG_ALERT_THRESHOLD": otp_hex(0xfffd0002),
                "CREATOR_SW_CFG_RNG_HEALTH_CONFIG_DIGEST": otp_hex(0x8264cf75),
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
                # Enable bootstrap. See `hardened_bool_t` in
                # sw/device/lib/base/hardened.h.
                "OWNER_SW_CFG_ROM_BOOTSTRAP_DIS": otp_hex(CONST.HARDENED_FALSE),
                # Set to 0x739 to use the ROM_EXT hash measurement as the key
                # manager attestation binding value.
                "OWNER_SW_CFG_ROM_KEYMGR_ROM_EXT_MEAS_EN": otp_hex(0x0),
                # Report errors without any redaction.
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
                    alert_list = EARLGREY_ALERTS,
                    # The ordering is "prod, prod_end, dev, rma"
                    default = "X, X, X, X",
                ),
                # Set the classifications to kAlertClassX. See `alert_class_t` in
                # sw/device/silicon_creator/lib/drivers/alert.h
                "OWNER_SW_CFG_ROM_LOCAL_ALERT_CLASSIFICATION": otp_alert_classification(
                    alert_list = EARLGREY_LOC_ALERTS,
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
                # By default, ROM_EXT's bootstrap feature should be disabled.
                "OWNER_SW_CFG_ROM_EXT_BOOTSTRAP_EN": otp_hex(CONST.HARDENED_FALSE),
            },
        ),
    ],
)
