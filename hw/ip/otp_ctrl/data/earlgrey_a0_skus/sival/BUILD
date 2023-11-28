# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load(
    "//rules:const.bzl",
    "CONST",
    "get_lc_items",
)
load(
    "//rules:otp.bzl",
    "otp_hex",
    "otp_image",
    "otp_image_consts",
    "otp_json",
    "otp_partition",
)

package(default_visibility = ["//visibility:public"])

# Partition used to set a fixed seed value in `otp_image_consts` targets.
otp_json(
    name = "otp_json_baseline",
    seed = "85452983286950371191603618368782861611109037138182535346147818831008789508651",
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
    "//hw/ip/otp_ctrl/data/earlgrey_a0_skus/generic:alert_digest_cfg",
    "//hw/ip/otp_ctrl/data/earlgrey_a0_skus/generic:otp_json_creator_sw_cfg",
    "//hw/ip/otp_ctrl/data/earlgrey_a0_skus/sival:otp_json_manuf_state_creator_sival",
    "//hw/ip/otp_ctrl/data/earlgrey_a0_skus/generic:otp_json_owner_sw_cfg",
]

# The `MANUF_INDIVIDUALIZED` OTP profile configures the HW_CFG, CREATOR_SW and
# OWNER_SW OTP partitions. It also includes the `MANUF_INITIALIZED`.
MANUF_INDIVIDUALIZED = MANUF_INITIALIZED + MANUF_SW_INITIALIZED + [
    "//hw/ip/otp_ctrl/data:otp_json_hw_cfg",
]

# The `MANUF_PERSONALIZED` OTP profile configures the SECRET1 and SECRET2 OTP
# partitions. It also includes the `MANUF_INDIVIDUALIZED` profile.
MANUF_PERSONALIZED = MANUF_INDIVIDUALIZED + [
    "//hw/ip/otp_ctrl/data:otp_json_secret1",
    "//hw/ip/otp_ctrl/data:otp_json_fixed_secret2",
]

otp_json(
    name = "otp_json_manuf_state_creator_sival",
    partitions = [
        otp_partition(
            name = "CREATOR_SW_CFG",
            items = {
                "CREATOR_SW_CFG_MANUF_STATE": otp_hex(CONST.MANUF_STATE.SIVAL),
            },
        ),
    ],
)

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
    overlays = [
        "//hw/ip/otp_ctrl/data:otp_json_exec_disabled",
    ],
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
