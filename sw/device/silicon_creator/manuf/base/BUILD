# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@bazel_skylib//rules:common_settings.bzl", "bool_flag")
load(
    "//rules/opentitan:defs.bzl",
    "fpga_params",
    "opentitan_binary",
    "opentitan_test",
    "silicon_params",
)
load(
    "//sw/device/silicon_creator/manuf/base:provisioning_inputs.bzl",
    "CLOUD_KMS_CERT_ENDORSEMENT_PARAMS",
    "CP_PROVISIONING_INPUTS",
    "EARLGREY_A0_INDIVIDUALIZE_OTP_SW_CFGS",
    "FT_PERSONALIZE_KEYS",
    "FT_PROVISIONING_INPUTS",
    "LOCAL_CERT_ENDORSEMENT_PARAMS",
)

package(default_visibility = ["//visibility:public"])

cc_library(
    name = "flash_info_permissions",
    srcs = ["flash_info_permissions.h"],
    deps = ["//sw/device/lib/dif:flash_ctrl"],
)

opentitan_binary(
    name = "sram_cp_provision",
    testonly = True,
    srcs = ["sram_cp_provision.c"],
    exec_env = {
        "//hw/top_earlgrey:fpga_hyper310_rom_with_fake_keys": None,
        "//hw/top_earlgrey:fpga_cw340_rom_with_fake_keys": None,
        "//hw/top_earlgrey:silicon_creator": None,
    },
    kind = "ram",
    linker_script = "//sw/device/silicon_creator/manuf/lib:sram_program_linker_script",
    deps = [
        ":flash_info_permissions",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/arch:device",
        "//sw/device/lib/base:abs_mmio",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/dif:flash_ctrl",
        "//sw/device/lib/dif:lc_ctrl",
        "//sw/device/lib/dif:otp_ctrl",
        "//sw/device/lib/dif:pinmux",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:flash_ctrl_testutils",
        "//sw/device/lib/testing:lc_ctrl_testutils",
        "//sw/device/lib/testing:otp_ctrl_testutils",
        "//sw/device/lib/testing:pinmux_testutils",
        "//sw/device/lib/testing/json:provisioning_data",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:ottf_console",
        "//sw/device/lib/testing/test_framework:ottf_test_config",
        "//sw/device/lib/testing/test_framework:status",
        "//sw/device/lib/testing/test_framework:ujson_ottf",
        "//sw/device/silicon_creator/manuf/data/ast:fake",
        "//sw/device/silicon_creator/manuf/lib:flash_info_fields",
        "//sw/device/silicon_creator/manuf/lib:individualize",
        "//sw/device/silicon_creator/manuf/lib:otp_fields",
        "//sw/device/silicon_creator/manuf/lib:sram_start_no_ast_init",
    ],
)

opentitan_binary(
    name = "sram_cp_provision_functest",
    testonly = True,
    srcs = ["sram_cp_provision_functest.c"],
    exec_env = {
        "//hw/top_earlgrey:fpga_hyper310_rom_with_fake_keys": None,
        "//hw/top_earlgrey:fpga_cw340_rom_with_fake_keys": None,
        "//hw/top_earlgrey:silicon_creator": None,
    },
    kind = "ram",
    linker_script = "//sw/device/silicon_creator/manuf/lib:sram_program_linker_script",
    deps = [
        ":flash_info_permissions",
        "//hw/ip/otp_ctrl/data:otp_ctrl_c_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/arch:device",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/dif:flash_ctrl",
        "//sw/device/lib/dif:lc_ctrl",
        "//sw/device/lib/dif:otp_ctrl",
        "//sw/device/lib/dif:pinmux",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:flash_ctrl_testutils",
        "//sw/device/lib/testing:lc_ctrl_testutils",
        "//sw/device/lib/testing:otp_ctrl_testutils",
        "//sw/device/lib/testing:pinmux_testutils",
        "//sw/device/lib/testing/json:provisioning_data",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:ottf_console",
        "//sw/device/lib/testing/test_framework:ottf_test_config",
        "//sw/device/lib/testing/test_framework:status",
        "//sw/device/lib/testing/test_framework:ujson_ottf",
        "//sw/device/silicon_creator/manuf/lib:flash_info_fields",
        "//sw/device/silicon_creator/manuf/lib:individualize",
        "//sw/device/silicon_creator/manuf/lib:otp_fields",
        "//sw/device/silicon_creator/manuf/lib:sram_start",
    ],
)

_CP_PROVISIONING_CMD_ARGS = """
  --elf={sram_cp_provision}
""" + CP_PROVISIONING_INPUTS

_CP_PROVISIONING_HARNESS = "//sw/host/provisioning/cp"

opentitan_test(
    name = "cp_provision",
    exec_env = {
        "//hw/top_earlgrey:fpga_hyper310_rom_with_fake_keys": None,
        "//hw/top_earlgrey:fpga_cw340_rom_with_fake_keys": None,
        "//hw/top_earlgrey:silicon_creator": None,
    },
    fpga = fpga_params(
        binaries = {":sram_cp_provision": "sram_cp_provision"},
        changes_otp = True,
        needs_jtag = True,
        otp = "//hw/ip/otp_ctrl/data/earlgrey_skus/sival:otp_img_test_unlocked0_manuf_empty",
        tags = ["manuf"],
        test_cmd = _CP_PROVISIONING_CMD_ARGS,
        test_harness = _CP_PROVISIONING_HARNESS,
    ),
    silicon = silicon_params(
        binaries = {":sram_cp_provision": "sram_cp_provision"},
        changes_otp = True,
        interface = "teacup",
        needs_jtag = True,
        test_cmd = _CP_PROVISIONING_CMD_ARGS,
        test_harness = _CP_PROVISIONING_HARNESS,
    ),
)

opentitan_test(
    name = "cp_provision_functest",
    exec_env = {
        "//hw/top_earlgrey:fpga_hyper310_rom_with_fake_keys": None,
        "//hw/top_earlgrey:fpga_cw340_rom_with_fake_keys": None,
    },
    fpga = fpga_params(
        binaries = {
            ":sram_cp_provision": "sram_cp_provision",
            ":sram_cp_provision_functest": "sram_cp_provision_functest",
        },
        changes_otp = True,
        needs_jtag = True,
        otp = "//hw/ip/otp_ctrl/data:img_raw",
        tags = ["manuf"],
        test_cmd = """
            --provisioning-sram-elf={sram_cp_provision}
            --test-sram-elf={sram_cp_provision_functest}
        """ + CP_PROVISIONING_INPUTS,
        test_harness = "//sw/host/tests/manuf/cp_provision_functest",
    ),
)

[
    opentitan_binary(
        name = "sram_ft_individualize_{}".format(otp_sw_cfgs),
        testonly = True,
        srcs = ["sram_ft_individualize.c"],
        exec_env = {
            "//hw/top_earlgrey:fpga_hyper310_rom_with_fake_keys": None,
            "//hw/top_earlgrey:fpga_cw340_rom_with_fake_keys": None,
            "//hw/top_earlgrey:silicon_creator": None,
        },
        kind = "ram",
        linker_script = "//sw/device/silicon_creator/manuf/lib:sram_program_linker_script",
        deps = [
            ":flash_info_permissions",
            "//hw/top_earlgrey/sw/autogen:top_earlgrey",
            "//sw/device/lib/arch:device",
            "//sw/device/lib/base:macros",
            "//sw/device/lib/dif:flash_ctrl",
            "//sw/device/lib/dif:otp_ctrl",
            "//sw/device/lib/dif:pinmux",
            "//sw/device/lib/runtime:hart",
            "//sw/device/lib/runtime:log",
            "//sw/device/lib/testing:flash_ctrl_testutils",
            "//sw/device/lib/testing:otp_ctrl_testutils",
            "//sw/device/lib/testing:pinmux_testutils",
            "//sw/device/lib/testing/test_framework:check",
            "//sw/device/lib/testing/test_framework:ottf_console",
            "//sw/device/lib/testing/test_framework:ottf_test_config",
            "//sw/device/lib/testing/test_framework:status",
            "//sw/device/lib/testing/test_framework:ujson_ottf",
            "//sw/device/silicon_creator/manuf/lib:flash_info_fields",
            "//sw/device/silicon_creator/manuf/lib:individualize",
            "//sw/device/silicon_creator/manuf/lib:otp_fields",
            "//sw/device/silicon_creator/manuf/lib:sram_start",
            "//sw/device/silicon_creator/manuf/lib:individualize_sw_cfg_earlgrey_sku_{}".format(otp_sw_cfgs),
        ],
    )
    for otp_sw_cfgs in EARLGREY_A0_INDIVIDUALIZE_OTP_SW_CFGS
]

filegroup(
    name = "sram_ft_individualize_all",
    testonly = True,
    srcs = [
        ":sram_ft_individualize_prodc",
        ":sram_ft_individualize_sival",
    ],
)

cc_library(
    name = "ft_personalize_base",
    srcs = ["ft_personalize.c"],
    deps = [
        "//sw/device/lib/crypto/drivers:entropy",
        "//sw/device/lib/dif:flash_ctrl",
        "//sw/device/lib/dif:lc_ctrl",
        "//sw/device/lib/dif:otp_ctrl",
        "//sw/device/lib/dif:rstmgr",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:lc_ctrl_testutils",
        "//sw/device/lib/testing:rstmgr_testutils",
        "//sw/device/lib/testing/json:provisioning_data",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/lib/testing/test_framework:status",
        "//sw/device/lib/testing/test_framework:ujson_ottf",
        "//sw/device/silicon_creator/lib:attestation",
        "//sw/device/silicon_creator/lib:otbn_boot_services",
        "//sw/device/silicon_creator/lib/base:util",
        "//sw/device/silicon_creator/lib/cert",
        "//sw/device/silicon_creator/lib/cert:cdi_0_template_library",
        "//sw/device/silicon_creator/lib/cert:cdi_1_template_library",
        "//sw/device/silicon_creator/lib/cert:dice",
        "//sw/device/silicon_creator/lib/cert:tpm_ek_template_library",
        "//sw/device/silicon_creator/lib/cert:uds_template_library",
        "//sw/device/silicon_creator/lib/drivers:flash_ctrl",
        "//sw/device/silicon_creator/lib/drivers:hmac",
        "//sw/device/silicon_creator/lib/drivers:keymgr",
        "//sw/device/silicon_creator/lib/drivers:kmac",
        "//sw/device/silicon_creator/manuf/base:perso_tlv_data",
        "//sw/device/silicon_creator/manuf/lib:flash_info_fields",
        "//sw/device/silicon_creator/manuf/lib:individualize_sw_cfg_earlgrey_sku_sival",
        "//sw/device/silicon_creator/manuf/lib:personalize",
    ],
)

cc_library(
    name = "tpm_perso_fw_ext",
    srcs = ["tpm_personalize_ext.c"],
    deps = [
        "//sw/device/lib/dif:flash_ctrl",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:status",
        "//sw/device/lib/testing/test_framework:ujson_ottf",
        "//sw/device/silicon_creator/lib:attestation",
        "//sw/device/silicon_creator/lib/cert",
        "//sw/device/silicon_creator/lib/cert:tpm",
        "//sw/device/silicon_creator/lib/cert:tpm_ek_template_library",
        "//sw/device/silicon_creator/lib/drivers:flash_ctrl",
        "//sw/device/silicon_creator/lib/drivers:hmac",
        "//sw/device/silicon_creator/manuf/base:perso_tlv_data",
        "//sw/device/silicon_creator/manuf/lib:personalize",
    ],
)

cc_library(
    name = "perso_tlv_data",
    srcs = ["perso_tlv_data.c"],
    deps = [
        ":perso_tlv_headers",
        "//sw/device/lib/runtime:log",
        "//sw/device/silicon_creator/lib/cert",
    ],
)

# Need a separate library for the headers, because adding a dependency on
#//sw/device/silicon_creator/lib/cert required by perso_tlv_data above causes
# bindgen failures due to otbn (which is a cert dependency) requiring risc32
# environment.
cc_library(
    name = "perso_tlv_headers",
    hdrs = ["perso_tlv_data.h"],
    deps = [
        "//sw/device/lib/base:status",
        "//sw/device/lib/testing/json:provisioning_data",
    ],
)

_FT_PERSO_EXTS = [
    {
        "suffix": "",
        "ext_libs": ["@provisioning_exts//:perso_fw_ext"],
    },
    {
        "suffix": "_tpm_ext",
        "ext_libs": [":tpm_perso_fw_ext"],
    },
]

[
    opentitan_binary(
        name = "ft_personalize{}".format(ext["suffix"]),
        testonly = True,
        srcs = ["ft_personalize.c"],
        ecdsa_key = {"//sw/device/silicon_creator/rom/keys/fake/ecdsa:prod_key_0_ecdsa_p256": "prod_key_0"},
        exec_env = {
            "//hw/top_earlgrey:fpga_hyper310_rom_with_fake_keys": None,
            "//hw/top_earlgrey:fpga_cw340_rom_with_fake_keys": None,
            "//hw/top_earlgrey:silicon_creator": None,
        },
        linker_script = "//sw/device/lib/testing/test_framework:ottf_ld_silicon_creator_slot_a",
        spx_key = {"//sw/device/silicon_creator/rom/keys/fake/spx:prod_key_0_spx": "prod_key_0"},
        deps = [":ft_personalize_base"] + ext["ext_libs"],
    )
    for ext in _FT_PERSO_EXTS
]

config_setting(
    name = "ckms_cert_endorsement_params",
    flag_values = {":endorse_certs_with_ckms": "True"},
)

bool_flag(
    name = "endorse_certs_with_ckms",
    build_setting_default = False,
)

_FT_PROVISIONING_CMD_ARGS = """
  --elf={sram_ft_individualize}
  --bootstrap={ft_personalize}
""" + FT_PROVISIONING_INPUTS + select({
    ":ckms_cert_endorsement_params": CLOUD_KMS_CERT_ENDORSEMENT_PARAMS,
    "//conditions:default": LOCAL_CERT_ENDORSEMENT_PARAMS,
})

_FT_PROVISIONING_HARNESS = "//sw/host/provisioning/ft"

[
    opentitan_test(
        name = "ft_provision{}".format(ext["suffix"]),
        exec_env = {
            "//hw/top_earlgrey:fpga_hyper310_rom_with_fake_keys": None,
            "//hw/top_earlgrey:fpga_cw340_rom_with_fake_keys": None,
            "//hw/top_earlgrey:silicon_creator": None,
        },
        fpga = fpga_params(
            timeout = "long",
            binaries = {
                ":sram_ft_individualize_sival": "sram_ft_individualize",
                ":ft_personalize{}".format(ext["suffix"]): "ft_personalize",
            },
            changes_otp = True,
            data = FT_PERSONALIZE_KEYS,
            needs_jtag = True,
            otp = "//hw/ip/otp_ctrl/data/earlgrey_skus/sival:otp_img_test_locked0_manuf_initialized",
            tags = [
                "lc_test_locked0",
                "manuf",
            ],
            test_cmd = _FT_PROVISIONING_CMD_ARGS,
            test_harness = _FT_PROVISIONING_HARNESS,
        ),
        silicon = silicon_params(
            binaries = {
                ":sram_ft_individualize_sival": "sram_ft_individualize",
                ":ft_personalize{}".format(ext["suffix"]): "ft_personalize",
            },
            changes_otp = True,
            data = FT_PERSONALIZE_KEYS,
            interface = "teacup",
            needs_jtag = True,
            test_cmd = _FT_PROVISIONING_CMD_ARGS,
            test_harness = _FT_PROVISIONING_HARNESS,
        ),
    )
    for ext in _FT_PERSO_EXTS
]
