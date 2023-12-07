# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:linker.bzl", "ld_library")
load(
    "//rules/opentitan:defs.bzl",
    "OPENTITAN_CPU",
    "cw310_params",
    "hyper310_jtag_params",
    "opentitan_test",
)
load(
    "//sw/device/silicon_creator/manuf:provisioning_inputs.bzl",
    "EARLGREY_A0_INDIVIDUALIZE_OTP_SW_CFGS",
)

package(default_visibility = ["//visibility:public"])

ld_library(
    name = "sram_program_linker_script",
    # We want to avoid page alignment since the SRAM program is not loaded at the beginning of the
    # SRAM and we the generated ELF segment should not contain any headers (as this could overwrite
    # some SRAM content)
    non_page_aligned_segments = True,
    script = "sram_program.ld",
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey_memory",
        "//sw/device:info_sections",
        "//sw/device/silicon_creator/lib/base:static_critical_sections",
    ],
)

cc_library(
    name = "sram_start_headers",
    hdrs = ["sram_start.h"],
)

cc_library(
    name = "sram_start",
    srcs = ["sram_start.S"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        ":ast_program",
        ":sram_start_headers",
        "//hw/ip/csrng/data:csrng_regs",
        "//hw/ip/edn/data:edn_regs",
        "//hw/ip/entropy_src/data:entropy_src_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/crt",
        "//sw/device/lib/testing/test_framework:ottf_isrs",
    ],
)

cc_library(
    name = "flash_info_fields",
    srcs = ["flash_info_fields.c"],
    hdrs = ["flash_info_fields.h"],
    deps = [
        "//hw/ip/otp_ctrl/data:otp_ctrl_regs",
        "//hw/top_earlgrey/ip/ast/data:ast_regs",
        "//hw/top_earlgrey/ip/flash_ctrl/data/autogen:flash_ctrl_regs",
        "//sw/device/lib/base:status",
        "//sw/device/lib/dif:flash_ctrl",
        "//sw/device/lib/testing:flash_ctrl_testutils",
        "//sw/device/silicon_creator/lib:attestation",
    ],
)

cc_library(
    name = "otp_fields",
    srcs = ["otp_fields.c"],
    hdrs = ["otp_fields.h"],
    deps = [
        "//hw/ip/otp_ctrl/data:otp_ctrl_regs",
        "//sw/device/lib/base:bitfield",
    ],
)

cc_library(
    name = "otp_img_types",
    hdrs = ["otp_img_types.h"],
)

cc_library(
    name = "util",
    srcs = ["util.c"],
    hdrs = ["util.h"],
    deps = [
        "//hw/ip/otp_ctrl/data:otp_ctrl_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:status",
        "//sw/device/lib/crypto/impl:hash",
        "//sw/device/lib/crypto/include:datatypes",
        "//sw/device/lib/dif:otp_ctrl",
        "//sw/device/lib/testing:otp_ctrl_testutils",
    ],
)

cc_library(
    name = "individualize",
    srcs = ["individualize.c"],
    hdrs = ["individualize.h"],
    deps = [
        ":flash_info_fields",
        ":otp_fields",
        ":util",
        "//sw/device/lib/base:bitfield",
        "//sw/device/lib/base:multibits",
        "//sw/device/lib/base:status",
        "//sw/device/lib/crypto/drivers:entropy",
        "//sw/device/lib/crypto/impl:hash",
        "//sw/device/lib/crypto/include:datatypes",
        "//sw/device/lib/dif:flash_ctrl",
        "//sw/device/lib/dif:lc_ctrl",
        "//sw/device/lib/dif:otp_ctrl",
        "//sw/device/lib/testing:flash_ctrl_testutils",
        "//sw/device/lib/testing:lc_ctrl_testutils",
        "//sw/device/lib/testing:otp_ctrl_testutils",
        "//sw/device/lib/testing/json:provisioning_data",
        "//sw/device/lib/testing/test_framework:check",
    ],
)

opentitan_test(
    name = "individualize_functest",
    srcs = ["individualize_functest.c"],
    cw310 = cw310_params(
        bitstream = "//hw/bitstream:rom_with_fake_keys_otp_test_unlocked1_initial",
        tags = ["manuf"],
    ),
    exec_env = {
        "//hw/top_earlgrey:fpga_cw310_rom_with_fake_keys": None,
    },
    rsa_key = {"//sw/device/silicon_creator/rom/keys/fake/rsa:test_private_key_0": "test_key_0"},
    deps = [
        ":individualize",
        ":otp_fields",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:status",
        "//sw/device/lib/dif:flash_ctrl",
        "//sw/device/lib/dif:lc_ctrl",
        "//sw/device/lib/dif:otp_ctrl",
        "//sw/device/lib/dif:rstmgr",
        "//sw/device/lib/testing:lc_ctrl_testutils",
        "//sw/device/lib/testing:rstmgr_testutils",
        "//sw/device/lib/testing/json:provisioning_data",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

cc_library(
    name = "individualize_sw_cfg",
    srcs = [
        "individualize_sw_cfg.c",
        "individualize_sw_cfg.h",
    ],
    deps = [
        ":flash_info_fields",
        ":otp_img_types",
        ":util",
        "//hw/ip/otp_ctrl/data:otp_ctrl_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:status",
        "//sw/device/lib/dif:flash_ctrl",
        "//sw/device/lib/dif:otp_ctrl",
        "//sw/device/lib/testing:flash_ctrl_testutils",
        "//sw/device/lib/testing:otp_ctrl_testutils",
    ],
)

# As more SKUs are created with different OTP software configuration partitions,
# libraries can be added to INDIVIDUALIZE_OTP_SW_CFGS accordingly.
[
    cc_library(
        name = "individualize_sw_cfg_earlgrey_a0_sku_{}".format(otp_sw_cfg),
        deps = [
            ":individualize_sw_cfg",
            "//hw/ip/otp_ctrl/data/earlgrey_a0_skus/{}:otp_sw_cfg".format(otp_sw_cfg),
        ],
    )
    for otp_sw_cfg in EARLGREY_A0_INDIVIDUALIZE_OTP_SW_CFGS
]

opentitan_test(
    name = "individualize_sw_cfg_functest",
    srcs = ["individualize_sw_cfg_functest.c"],
    cw310 = cw310_params(
        bitstream = "//hw/bitstream:rom_with_fake_keys_otp_test_unlocked1",
        tags = ["manuf"],
        test_cmd = """
        --clear-bitstream
        --bitstream={bitstream}
        --bootstrap={firmware}
        """,
        test_harness = "//sw/host/tests/manuf/individualize_sw_cfg",
    ),
    exec_env = {
        "//hw/top_earlgrey:fpga_cw310_rom_with_fake_keys": None,
    },
    deps = [
        ":flash_info_fields",
        ":individualize_sw_cfg_earlgrey_a0_sku_sival_bringup",
        "//hw/ip/otp_ctrl/data:otp_ctrl_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:status",
        "//sw/device/lib/dif:flash_ctrl",
        "//sw/device/lib/dif:otp_ctrl",
        "//sw/device/lib/dif:rstmgr",
        "//sw/device/lib/runtime:hart",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:flash_ctrl_testutils",
        "//sw/device/lib/testing:otp_ctrl_testutils",
        "//sw/device/lib/testing:rstmgr_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

cc_library(
    name = "personalize",
    srcs = ["personalize.c"],
    hdrs = ["personalize.h"],
    deps = [
        ":flash_info_fields",
        ":otp_fields",
        ":util",
        "//sw/device/lib/base:multibits",
        "//sw/device/lib/base:status",
        "//sw/device/lib/crypto/drivers:entropy",
        "//sw/device/lib/crypto/impl:aes",
        "//sw/device/lib/crypto/impl:ecc",
        "//sw/device/lib/crypto/impl:hash",
        "//sw/device/lib/crypto/impl:keyblob",
        "//sw/device/lib/crypto/include:datatypes",
        "//sw/device/lib/dif:flash_ctrl",
        "//sw/device/lib/dif:lc_ctrl",
        "//sw/device/lib/dif:otp_ctrl",
        "//sw/device/lib/testing:flash_ctrl_testutils",
        "//sw/device/lib/testing:lc_ctrl_testutils",
        "//sw/device/lib/testing:otp_ctrl_testutils",
        "//sw/device/lib/testing/json:provisioning_data",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/silicon_creator/lib:attestation",
    ],
)

opentitan_test(
    name = "personalize_functest",
    srcs = ["personalize_functest.c"],
    cw310 = hyper310_jtag_params(
        data = ["//sw/device/silicon_creator/manuf/keys/fake:rma_unlock_token_export_key.sk_hsm.der"],
        otp = "//hw/ip/otp_ctrl/data/earlgrey_a0_skus/sival_bringup:otp_img_dev_manuf_individualized",
        tags = [
            "lc_dev",
            "manuf",
        ],
        test_cmd = """
            --bootstrap={firmware}
            --host-ecc-sk="$(rootpath //sw/device/silicon_creator/manuf/keys/fake:rma_unlock_token_export_key.sk_hsm.der)"
        """,
        test_harness = "//sw/host/tests/manuf/personalize",
    ),
    exec_env = {
        "//hw/top_earlgrey:fpga_cw310_sival": None,
    },
    rsa_key = {"//sw/device/silicon_creator/rom/keys/fake/rsa:dev_private_key_0": "dev_key_0"},
    deps = [
        ":flash_info_fields",
        ":personalize",
        "//hw/ip/flash_ctrl/data:flash_ctrl_regs",
        "//hw/ip/lc_ctrl/data:lc_ctrl_regs",
        "//hw/ip/otp_ctrl/data:otp_ctrl_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:status",
        "//sw/device/lib/dif:flash_ctrl",
        "//sw/device/lib/dif:lc_ctrl",
        "//sw/device/lib/dif:otp_ctrl",
        "//sw/device/lib/dif:rstmgr",
        "//sw/device/lib/testing:rstmgr_testutils",
        "//sw/device/lib/testing/json:command",
        "//sw/device/lib/testing/json:provisioning_data",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/lib/testing/test_framework:ujson_ottf",
        "//sw/device/silicon_creator/lib:attestation",
        "//sw/device/silicon_creator/lib/drivers:retention_sram",
    ],
)

cc_library(
    name = "ast_program",
    srcs = ["ast_program.c"],
    deps = [
        ":flash_info_fields",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:status",
        "//sw/device/lib/dif:flash_ctrl",
        "//sw/device/lib/dif:pinmux",
        "//sw/device/lib/dif:uart",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/runtime:print",
    ],
)

opentitan_test(
    name = "ast_program_functest",
    srcs = [
        "ast_program.c",
        "ast_program_functest.c",
    ],
    defines = [
        "AST_PROGRAM_UNITTEST=1",
    ],
    exec_env = {
        "//hw/top_earlgrey:fpga_cw310_test_rom": None,
    },
    deps = [
        ":flash_info_fields",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:status",
        "//sw/device/lib/dif:flash_ctrl",
        "//sw/device/lib/dif:pinmux",
        "//sw/device/lib/dif:uart",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/runtime:print",
        "//sw/device/lib/testing:flash_ctrl_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/lib:crc32",
    ],
)
