# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:autogen.bzl", "autogen_hjson_header")
load(
    "//rules:otp.bzl",
    "STD_OTP_OVERLAYS",
    "STD_OTP_OVERLAYS_WITHOUT_SECRET_PARTITIONS",
    "otp_alert_classification",
    "otp_alert_digest",
    "otp_bytestring",
    "otp_hex",
    "otp_image",
    "otp_json",
    "otp_partition",
    "otp_per_class_bytes",
    "otp_per_class_ints",
    "otp_per_class_lists",
)
load("@rules_pkg//pkg:mappings.bzl", "pkg_files")
load("@bazel_skylib//rules:common_settings.bzl", "int_flag", "string_flag")
load("//rules:const.bzl", "CONST")
load("//rules:const-darjeeling.bzl", "DARJEELING_ALERTS", "DARJEELING_LOC_ALERTS")

package(default_visibility = ["//visibility:public"])

# These configurations expose the OTP image generation tool's command line
# arguments to enable dvsim to pass this through Bazel to the underlying OTP
# image generation script. This is required to enable dvsim to invoke OTP image
# generation as part of the Bazel build process, while still enabling the use of
# multiple seeds needed to achieve DV coverage.
int_flag(
    name = "img_seed",
    build_setting_default = 0,
)

string_flag(
    name = "lc_seed",
    # Default must match value in hw/ip/lc_ctrl/data/lc_ctrl.hjson.
    build_setting_default = "40182201019264397688411770949626922549663256047001778394918990008320537410392",
)

string_flag(
    name = "otp_seed",
    # Default must match value in hw/ip/otp_ctrl/data/otp_ctrl_mmap.hjson.
    build_setting_default = "36021179872380457113239299468132194022238108125576166239904535336103582949069",
)

string_flag(
    name = "data_perm",
    build_setting_default = "",
)

# This package must be kept in sync with get_otp_images() from //rules:otp.bzl.
# That is, each OTP image referenced by the macro should have a definition in
# this BUILD file.

filegroup(
    name = "all_files",
    srcs = glob(["**"]),
)

exports_files(["otp_ctrl_img.h.tpl"])

autogen_hjson_header(
    name = "otp_ctrl_regs",
    srcs = [
        "otp_ctrl.hjson",
    ],
    interface = "core",
)

exports_files(["otp_ctrl_mmap.hjson"])

otp_json(
    name = "otp_json_creator_sw_cfg",
    partitions = [
        otp_partition(
            name = "CREATOR_SW_CFG",
            items = {
                # Use software mod_exp implementation for signature
                # verification. See the definition of `hardened_bool_t` in
                # sw/lib/sw/device/base/hardened.h.
                "CREATOR_SW_CFG_SIGVERIFY_RSA_MOD_EXP_IBEX_EN": otp_hex(CONST.HARDENED_TRUE),
                # Mark the first three keys as valid and remaining as invalid
                # since we currently have only three keys. See the definition of
                # `hardened_byte_bool_t` in sw/lib/sw/device/base/hardened.h.
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
                # sw/lib/sw/device/silicon_creator/sigverify/spx_verify.h.
                "CREATOR_SW_CFG_SIGVERIFY_SPX_EN": otp_hex(0x8d6c8c17),
                # Enable use of entropy for countermeasures. See the definition
                # of `hardened_bool_t` in sw/lib/sw/device/base/hardened.h.
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
                # sw/lib/sw/device/base/hardened.h.
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

# CREATOR_SW_CFG configuration for TEST_UNLOCKED lifecycle device states.
# Configures OTP values required to enable ROM execution. All other values are
# configured with the `otp_json_creator_sw_cfg` rule.
otp_json(
    name = "otp_json_creator_sw_cfg_test_unlocked",
    partitions = [
        otp_partition(
            name = "CREATOR_SW_CFG",
            items = {
                # ROM execution is enabled if this item is set to a non-zero
                # value.
                "CREATOR_SW_CFG_ROM_EXEC_EN": otp_hex(0xffffffff),
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
                # sw/lib/sw/device/base/hardened.h.
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
)

otp_json(
    name = "otp_json_hw_cfg",
    partitions = [
        otp_partition(
            name = "HW_CFG0",
            items = {
                "DEVICE_ID": "<random>",
            },
            lock = True,
        ),
    ],
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
    name = "otp_json_secret2",
    partitions = [
        otp_partition(
            name = "SECRET2",
            items = {
                "RMA_TOKEN": "<random>",
                "CREATOR_ROOT_KEY_SHARE0": "<random>",
                "CREATOR_ROOT_KEY_SHARE1": "<random>",
            },
            lock = True,
        ),
    ],
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
            },
            lock = False,
        ),
    ],
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
    seed = "52408960416235844780753299194502148156786072650816676092165912261205302331741",
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
        seed = "52408960416235844780753299194502148156786072650816676092165912261205302331741",
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
        seed = "52408960416235844780753299194502148156786072650816676092165912261205302331741",
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
    seed = "85452983286950371191603618368782861611109037138182535346147818831008789508651",
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
    seed = "113517944176559405110937879233240229311794601727326023435899657066678782830485",
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
    seed = "113517944176559405110937879233240229311794601727326023435899657066678782830485",
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
    seed = "52408960416235844780753299194502148156786072650816676092165912261205302331741",
)

otp_json(
    name = "otp_json_patch",
    partitions = [
        otp_partition(
            name = "ROM_PATCH",
            items = {
                "ROM_PATCH_DATA": "a842a163d163f2120f25bf190f16493f03f1093e5061ebccf077c097e8c06d1b85bb5e68f2b2bac21fbe167b1cc92d2b615c8d070796ac37f47c5cb34156da08f5e07d038289f2bf1960df80135c802dde98087f2762b8859f919f67f6502f5510ee02e2256ba8af07e69bab50485963825447a4610b61aa5587b609d3a84c78f0396af1b95a97b537112ab5d2175e6711690cef8add64534e22f0647b4bc7b6db85b28a75a8a7d3db803299efca61956e28549f89cbfc5cbddd8b0280294bfb0b472c3db158abea4486a95283fed98ac3be0760ee4cc0454434be92adf433719d4c48ab78d9c01c5a88e51c8402a0ebd44df2497152b59f5c04d34ec4a7cee6c281d4c833d6b2e87b521d3789e567c330f1618d4ca04473ac406d55b2e9a553ff094f561111908b32b12b66448144a77fc38abf80d9e050fc1075dd124f3073ebfe03379dab160c98075b5de7cef6f356a557ebf14e858e4310d2b0de241a1fdfb6412b32accb70e2fe6c6eb5bd2aba3a4ed9c4673b0202cf18d01dc70d63880d050563548a05963456789145678900000000130000001300000013000000130000001300000013000000130000001300000013000000130000001300000013000000130000001300000013000000130000001300000013000000130000001300000013000000130000001300000013000000130000001300000013000000130000001300000013000000130000001300000013000000130000001300000013000000130000001300000013000000130000001300000013000000130000001300000013000000130000001300000013000000130000001300000013000000130000001300000013000000130000001300000013000000130000001300000013000000130000001300000013000000130000001300000013000000130000001300000013000000130000001300000013000000130000001300000013000000130000001300000013000000130000001300000013000000130000001300000013000000130000001300000013000000130000001300000013000000130000001300000013000000130000001300000013000000130000001300000013000000130000001300000013000000130000001300000013000000130000001300000013000000130000001300000013000000130000001300000013000000130000001300000013000000130000001300000013000000130000001300000013548a059605a5051300b406075340065405a50513000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000400c9002084010004004100208201000400088020940020125060ad8168a85d277f57556ada1717b842a069b31bef3f43da95824e3054a6a3e68659e126106023d29b6552f492fe39d1f042f7d4b1fd727ccb2fe6561def721debfc6257d2e76761f1867a2e072dfc81e28be4e09a9e2d5b52f179e820fd2aa976199add63a5ef4d3a2e9a4ab0f957098f84ff034c9b32b8b050540e6b04ecb9b12bd70fcf91e200526d5d76920aba2a69a2d69ce33e5fe247af5474d1407fcab00893a5bda64fe145f76d0f54b5f43fa9aaf00009c19cee2c14d9daa746e15a2bd4f003c78b7cde65c23d3973150ac596358dfc34b03b9765d98483c59482bb13ad9439cdbfa08f3d51619de6fa2209f4252838e93389a34a44ad6b1d56681bc7ddaa37d9d24e0bca6c9ab4cb2bf05d12d8081b90a3d9a2a960bd6db66e6ab46e4d688505d20d8fd94232a46f9ad8eda610502fdf9020b754645e08c883337c041959d0efd957bf0d9a561d09ed799c187fb21bb3bead3dcedc2f2e89d563a66de3ee56b74c41ca868057edbd766d775179d9beaaedd174471d9dca7fe2632420d050563548a059600c60563534005930000001300000013000000130000001300000013000000130000001300000013000000130000001300000013000000130000001300000013000000130000001300000013000000130000001300000013000000130000001300000013000000130000001300000013000000130000001300000013000000130000001300000013000000130000001300000013000000130000001300000013000000130000001300000013000000130000001300000013000000130000001300000013000000130000001300000013000000130000001300000013000000130000001300000013000000130000001300000013000000130000001300b505635340059305a50513000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100040049000482010004000880089400100e506",
            },
        ),
    ],
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
            ":otp_json_creator_sw_cfg_test_unlocked",
        ],
    )
    for i in range(0, 8)
]

[
    otp_image(
        name = "img_test_locked{}".format(i),
        src = ":otp_json_test_locked{}".format(i),
        overlays = [
            ":otp_json_secret0",
            ":otp_json_creator_sw_cfg_test_unlocked",
        ],
    )
    for i in range(0, 7)
]

# Represents a DEV state OTP image emulating the state of the device after the
# exit test token has been applied and before running individualization.
# The following partitions are missing to ensure the image is initialize with
# default values: SECRET1, SECRET2, HW_CFG.
# The following partitions are expected to be configured in previous lifecycle
# stages: SECRET0, CREATOR_SW, OWNER_SW.
otp_image(
    name = "img_dev_initial",
    src = ":otp_json_dev",
    overlays = [
        ":otp_json_secret0",
        ":otp_json_creator_sw_cfg",
        ":otp_json_owner_sw_cfg",
        ":otp_json_alert_digest_cfg",
    ],
)

# Represents a device in DEV state with the SECRET0 and SECRET1 partitions in
# locked state. SECRET2 partition is unlocked.
otp_image(
    name = "img_dev_individualized",
    src = ":otp_json_dev",
    overlays = [
        ":otp_json_secret0",
        ":otp_json_secret1",
    ] + STD_OTP_OVERLAYS_WITHOUT_SECRET_PARTITIONS,
)

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

otp_image(
    name = "img_rma_patch",
    src = ":otp_json_rma",
    overlays = STD_OTP_OVERLAYS + [":otp_json_patch"],
)

# Create an execution-disabling overlay
otp_json(
    name = "otp_json_exec_disabled",
    partitions = [
        otp_partition(
            name = "CREATOR_SW_CFG",
            items = {"CREATOR_SW_CFG_ROM_EXEC_EN": otp_hex(0x0)},
        ),
    ],
)

otp_image(
    name = "img_exec_disabled",
    src = ":otp_json_rma",
    overlays = STD_OTP_OVERLAYS + [":otp_json_exec_disabled"],
)

# Create a bootstrap-disabling overlay
otp_json(
    name = "otp_json_bootstrap_disabled",
    partitions = [
        otp_partition(
            name = "OWNER_SW_CFG",
            items = {"OWNER_SW_CFG_ROM_BOOTSTRAP_DIS": otp_hex(CONST.HARDENED_TRUE)},
        ),
    ],
)

otp_image(
    name = "img_bootstrap_disabled",
    src = ":otp_json_rma",
    overlays = STD_OTP_OVERLAYS + [":otp_json_bootstrap_disabled"],
)

filegroup(
    name = "otp_imgs",
    srcs = [
        ":img_dev",
        ":img_dev_individualized",
        ":img_dev_initial",
        ":img_prod",
        ":img_raw",
        ":img_rma",
        ":img_rma_patch",
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
