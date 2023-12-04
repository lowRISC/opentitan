# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# SKU: SiVal Bringup. ASCII code `SV00`.
# The SiVal bringup SKU is intended to be use in early bring-up stages of
# Earl Grey silicon. Some of the countermeasures in the ROM are disabled to
# de-risk bring-up and provisioning tests.

load(
    "//rules:const.bzl",
    "CONST",
    "EARLGREY_ALERTS",
    "EARLGREY_LOC_ALERTS",
    "get_lc_items",
)
load(
    "//rules:otp.bzl",
    "otp_alert_classification",
    "otp_alert_digest",
    "otp_bytestring",
    "otp_hex",
    "otp_image",
    "otp_image_consts",
    "otp_json",
    "otp_partition",
    "otp_per_class_bytes",
    "otp_per_class_ints",
    "otp_per_class_lists",
)

package(default_visibility = ["//visibility:public"])

# Partition used to set a fixed seed value in `otp_image_consts` targets.
otp_json(
    name = "otp_json_baseline",
    seed = "85452983286950371191603618368782861611109037138182535346147818831008789508651",
)

otp_json(
    name = "otp_json_creator_sw_cfg",
    partitions = [
        otp_partition(
            name = "CREATOR_SW_CFG",
            items = {
                # Enable AST initialization.
                # CREATOR_SW_CFG_AST_CFG is handled by the manufacturing flow
                # and not listed directly in this configuration.
                "CREATOR_SW_CFG_AST_INIT_EN": otp_hex(CONST.MUBI4_TRUE),
                "CREATOR_SW_CFG_ROM_EXT_SKU": otp_hex(0x0),
                # Use software mod_exp implementation for signature
                # verification. See the definition of `hardened_bool_t` in
                # sw/device/lib/base/hardened.h.
                "CREATOR_SW_CFG_SIGVERIFY_RSA_MOD_EXP_IBEX_EN": otp_hex(CONST.HARDENED_FALSE),
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
                # The CREATOR_SW_CFG_SIGVERIFY_SPX_KEY_EN needs to be added
                # when SPX sigverify is enabled.
                "CREATOR_SW_CFG_SIGVERIFY_SPX_EN": otp_hex(0x8d6c8c17),
                # Enable flash data page scrambling and ECC.
                "CREATOR_SW_CFG_FLASH_DATA_DEFAULT_CFG": "0000090606",
                "CREATOR_SW_CFG_FLASH_INFO_BOOT_DATA_CFG": otp_hex(0x0),
                "CREATOR_SW_CFG_FLASH_HW_INFO_CFG_OVERRIDE": otp_hex(0x0),
                # Disable use of entropy for countermeasures. See the definition
                # of `hardened_bool_t` in sw/device/lib/base/hardened.h.
                "CREATOR_SW_CFG_RNG_EN": otp_hex(CONST.HARDENED_TRUE),
                "CREATOR_SW_CFG_JITTER_EN": otp_hex(CONST.MUBI4_TRUE),
                "CREATOR_SW_CFG_RET_RAM_RESET_MASK": otp_hex(0x0),
                "CREATOR_SW_CFG_MANUF_STATE": otp_hex(CONST.MANUF_STATE.SIVAL),
                # ROM execution is enabled if this item is set to a non-zero
                # value.
                "CREATOR_SW_CFG_ROM_EXEC_EN": otp_hex(0xffffffff),
                # Value to write to the cpuctrl CSR in `rom_init()`.
                # See:
                # https://ibex-core.readthedocs.io/en/latest/03_reference/cs_registers.html#cpu-control-register-cpuctrl
                # CPUCTRL = 0x1 enables ICACHE.
                "CREATOR_SW_CFG_CPUCTRL": otp_hex(0x1),
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
                # This enables a busyloop in the ROM to give time to
                # trigger an RMA lifecycle transition via JTAG.
                # TODO: The following value needs to be updated once we have an
                # idea of how many cycles are needed to enter RMA.
                "CREATOR_SW_CFG_RMA_SPIN_EN": otp_hex(CONST.HARDENED_TRUE),
                "CREATOR_SW_CFG_RMA_SPIN_CYCLES": otp_hex(0x2000000),
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

                # Any value different than `CONST.HARDENED_FALSE` will force
                # main SRAM scramble key rotation.
                "CREATOR_SW_CFG_SRAM_KEY_RENEW_EN": otp_hex(0x0),
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
                # Report errors without any redaction.
                "OWNER_SW_CFG_ROM_ERROR_REPORTING": otp_hex(CONST.SHUTDOWN.REDACT.NONE),
                # Enable bootstrap. See `hardened_bool_t` in
                # sw/device/lib/base/hardened.h.
                "OWNER_SW_CFG_ROM_BOOTSTRAP_DIS": otp_hex(CONST.HARDENED_FALSE),
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
                "OWNER_SW_CFG_ROM_WATCHDOG_BITE_THRESHOLD_CYCLES": otp_hex(0x0),
                # Set to 0x739 to use the ROM_EXT hash measurement as the key
                # manager attestation binding value. Since our attestation
                # scheme has changed, we keep this as false (disabled).
                "OWNER_SW_CFG_ROM_KEYMGR_ROM_EXT_MEAS_EN": otp_hex(0x0),
                "OWNER_SW_CFG_MANUF_STATE": otp_hex(0x0),
                "OWNER_SW_CFG_ROM_RSTMGR_INFO_EN": otp_hex(0x0),
                # Disable ROM_EXT recovery feature.
                "OWNER_SW_CFG_ROM_EXT_BOOTSTRAP_EN": otp_hex(0x0),
            },
        ),
    ],
)

# Create an overlay for the alert_handler digest.
otp_alert_digest(
    name = "alert_digest_cfg",
    otp_img = ":otp_json_owner_sw_cfg",
)

otp_json(
    name = "otp_json_hw_cfg",
    partitions = [
        otp_partition(
            name = "HW_CFG",
            items = {
                "DEVICE_ID": "<random>",
                # Enable code execution from SRAM in PROD state.
                "EN_SRAM_IFETCH": True,
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

otp_json(
    name = "otp_json_secret1",
    partitions = [
        otp_partition(
            name = "SECRET1",
            items = {
                "FLASH_ADDR_KEY_SEED": "<random>",
                "FLASH_DATA_KEY_SEED": "<random>",
                "SRAM_DATA_KEY_SEED": "<random>",
            },
            lock = True,
        ),
    ],
)

otp_json(
    name = "otp_json_fixed_secret2",
    partitions = [
        otp_partition(
            name = "SECRET2",
            items = {
                # We aren't testing keymgr for ROM_EXT tests and we want
                # reproducible bitstreams for all tests.
                "RMA_TOKEN": "0x1faf9056acde66561685549803a28bec",
                "CREATOR_ROOT_KEY_SHARE0": "1111111111111111111111111111111111111111111111111111111111111111",
                "CREATOR_ROOT_KEY_SHARE1": "2222222222222222222222222222222222222222222222222222222222222222",
            },
            lock = True,
        ),
    ],
)

# The `LC_MISSION_STATES` object contains the set of mission mode life cycle
# states. A device is considered to be mission mode configured if it has a
# matching `MANUF_PERSONALIZED` OTP configuration.
LC_MISSION_STATES = get_lc_items(
    CONST.LCV.DEV,
    CONST.LCV.PROD,
    CONST.LCV.PROD_END,
)

# The `MANUF_INITIALIZED` OTP profile configures the SECRET0 partition to
# enable the device to transition between test_unlock and test_locked states,
# as well as to transition out of test_unlock into any of the
# `LC_MISSION_STATES`.
MANUF_INITIALIZED = [
    "//hw/ip/otp_ctrl/data:otp_json_fixed_secret0",
]

MANUF_SW_INITIALIZED = [
    ":alert_digest_cfg",
    ":otp_json_creator_sw_cfg",
    ":otp_json_owner_sw_cfg",
]

# The `MANUF_INDIVIDUALIZED` OTP profile configures the HW_CFG, CREATOR_SW and
# OWNER_SW OTP partitions. It also includes the `MANUF_INITIALIZED`.
MANUF_INDIVIDUALIZED = MANUF_INITIALIZED + MANUF_SW_INITIALIZED + [
    ":otp_json_hw_cfg",
]

# The `MANUF_PERSONALIZED` OTP profile configures the SECRET1 and SECRET2 OTP
# partitions. It also includes the `MANUF_INDIVIDUALIZED` profile.
MANUF_PERSONALIZED = MANUF_INDIVIDUALIZED + [
    ":otp_json_secret1",
    ":otp_json_fixed_secret2",
]

# OTP SW Configuration. Used to generate a configuration program used during
# manufacturing. The `MANUF_SW_INITIALIZED` OTP profile is also used to derive
# OTP profiles representing the state of the device after running manufacturing
# steps consuming this dependency.
otp_image_consts(
    name = "otp_sw_cfg_c_file",
    src = ":otp_json_baseline",
    # Do not add additional overlays here. Update the `MANUF_SW_INITIALIZED`
    # OTP profile instead.
    overlays = MANUF_SW_INITIALIZED,
)

cc_library(
    name = "otp_sw_cfg",
    srcs = [":otp_sw_cfg_c_file"],
    deps = [
        "//hw/ip/otp_ctrl/data:otp_ctrl_regs",
        "//sw/device/silicon_creator/manuf/lib:otp_img_types",
    ],
)

# Initial test_unlocked state. Only applicable for test_unlocked0. All other
# test states require the SECRET0 partition to be configured.
# In this configuration, ROM execution is disabled by default. JTAG should be
# used to bootstrap code into SRAM or FLASH.
# See sw/device/tests/doc/sival/devguide.md for more details.
otp_image(
    name = "otp_img_test_unlocked0_manuf_empty",
    src = "//hw/ip/otp_ctrl/data:otp_json_test_unlocked0",
    visibility = ["//visibility:private"],
)

# `MANUF_INITIALIZED` configuration. This configuration will be generally used
# to lock the chips before shipping to the Final-Test test house.
# See sw/device/tests/doc/sival/devguide.md for more details.
otp_image(
    name = "otp_img_test_locked0_manuf_initialized",
    src = "//hw/ip/otp_ctrl/data:otp_json_test_locked0",
    overlays = MANUF_INITIALIZED,
)

# `MANUF_INITIALIZED` OTP configuration. Available on TEST_UNLOCK states 1-7.
# See sw/device/tests/doc/sival/devguide.md for more details.
[
    otp_image(
        name = "otp_img_test_unlocked{}_manuf_initialized".format(i),
        src = "//hw/ip/otp_ctrl/data:otp_json_test_unlocked{}".format(i),
        overlays = MANUF_INITIALIZED,
    )
    for i in range(1, 8)
]

# `MANUF_INDIVIDUALIZED` configuration. Available on TEST_UNLOCK states 1-7, as
# well as dev, prod, prod_end and rma. This configuration has flash scrambling
# disabled. See the personalized OTP configuration for targets requiring flash
# scrambling enabled.
# See sw/device/tests/doc/sival/devguide.md for more details.
[
    otp_image(
        name = "otp_img_{}_manuf_individualized".format(lc_state),
        src = "//hw/ip/otp_ctrl/data:otp_json_{}".format(lc_state),
        overlays = MANUF_INDIVIDUALIZED,
    )
    for lc_state, _ in get_lc_items(
        CONST.LCV.TEST_UNLOCKED1,
        CONST.LCV.TEST_UNLOCKED2,
        CONST.LCV.TEST_UNLOCKED3,
        CONST.LCV.TEST_UNLOCKED4,
        CONST.LCV.TEST_UNLOCKED5,
        CONST.LCV.TEST_UNLOCKED6,
        CONST.LCV.TEST_UNLOCKED7,
        CONST.LCV.DEV,
        CONST.LCV.PROD,
        CONST.LCV.PROD_END,
    )
]

# `MANUF_PERSONALIZED` configuration. Available on `LC_MISSION_STATES` life
# cycle states.
# See sw/device/tests/doc/sival/devguide.md for more details.
[
    otp_image(
        name = "otp_img_{}_manuf_personalized".format(lc_state),
        src = "//hw/ip/otp_ctrl/data:otp_json_{}".format(lc_state),
        overlays = MANUF_PERSONALIZED,
    )
    for lc_state, _ in LC_MISSION_STATES
]

# `MANUF_PERSONALIZED` configuration for RMA. Only available in secure environments.
otp_image(
    name = "otp_img_rma_manuf_personalized",
    src = "//hw/ip/otp_ctrl/data:otp_json_rma",
    overlays = MANUF_PERSONALIZED,
)
