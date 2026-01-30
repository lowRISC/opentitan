# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:manuf.bzl", "device_id_header")
load("//rules:signing.bzl", "offline_presigning_artifacts", "offline_signature_attach")
load("//rules:const.bzl", "CONST", "hex")
load("//rules:manifest.bzl", "manifest")
load("//rules/opentitan:cc.bzl", "opentitan_binary_assemble")
load(
    "//rules/opentitan:defs.bzl",
    "fpga_params",
    "opentitan_binary",
    "opentitan_test",
)
load(
    "//sw/device/silicon_creator/manuf/base:provisioning_inputs.bzl",
    "EARLGREY_SKUS",
    "disqualified_for_signing",
)
load(
    "//sw/device/silicon_creator/rom/e2e:defs.bzl",
    "SLOTS",
)
load(
    "//sw/device/silicon_creator/rom_ext:defs.bzl",
    "ROM_EXT_VERSION",
)
load(
    "//sw/device/silicon_creator/rom_ext/e2e:defs.bzl",
    "OWNER_SLOTS",
)
load("//rules:signing.bzl", "offline_presigning_artifacts", "offline_signature_attach")
load("@rules_pkg//pkg:tar.bzl", "pkg_tar")

package(default_visibility = ["//visibility:public"])

cc_library(
    name = "flash_info_permissions",
    srcs = ["flash_info_permissions.h"],
    deps = ["//sw/device/lib/dif:flash_ctrl"],
)

device_id_header(
    name = "cp_device_id",
    headers = ["cp_device_id.h"],
    mode = "cp",
    # All SKUs have the same CP device ID for a given product version so we just
    # use the emulation SKU configuration here.
    sku_config = "//sw/host/provisioning/orchestrator/configs/skus:emulation.hjson",
    template = ":cp_device_id.c.tpl",
)

opentitan_binary(
    name = "sram_cp_provision",
    testonly = True,
    srcs = ["sram_cp_provision.c"],
    exec_env = {
        "//hw/top_earlgrey:fpga_cw310_rom_with_fake_keys": None,
        "//hw/top_earlgrey:fpga_cw340_rom_with_fake_keys": None,
        "//hw/top_earlgrey:silicon_creator": None,
    },
    kind = "ram",
    linker_script = "//sw/device/silicon_creator/manuf/lib:sram_program_linker_script",
    deps = [
        ":cp_device_id_library",
        ":flash_info_permissions",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/arch:device",
        "//sw/device/lib/base:abs_mmio",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/crypto/drivers:entropy",
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
        "//sw/device/silicon_creator/manuf/lib:sram_start_no_ast_init",
    ],
)

opentitan_binary(
    name = "sram_cp_provision_functest",
    testonly = True,
    srcs = ["sram_cp_provision_functest.c"],
    exec_env = {
        "//hw/top_earlgrey:fpga_cw310_rom_with_fake_keys": None,
        "//hw/top_earlgrey:fpga_cw340_rom_with_fake_keys": None,
        "//hw/top_earlgrey:silicon_creator": None,
    },
    kind = "ram",
    linker_script = "//sw/device/silicon_creator/manuf/lib:sram_program_linker_script",
    deps = [
        ":cp_device_id_library",
        ":flash_info_permissions",
        "//hw/top:otp_ctrl_c_regs",
        "//hw/top/dt",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/arch:device",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/crypto/drivers:entropy",
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

opentitan_test(
    name = "cp_provision_functest",
    exec_env = {
        "//hw/top_earlgrey:fpga_cw310_rom_with_fake_keys": None,
        "//hw/top_earlgrey:fpga_cw340_rom_with_fake_keys": None,
    },
    fpga = fpga_params(
        timeout = "long",
        binaries = {
            ":sram_cp_provision": "sram_cp_provision",
            ":sram_cp_provision_functest": "sram_cp_provision_functest",
        },
        changes_otp = True,
        needs_jtag = True,
        otp = "//hw/top_earlgrey/data/otp:img_raw",
        tags = ["manuf"],
        test_cmd = """
            --provisioning-sram-elf={sram_cp_provision}
            --test-sram-elf={sram_cp_provision_functest}
        """,
        test_harness = "//sw/host/tests/manuf/cp_provision_functest",
    ),
)

[
    device_id_header(
        name = "ft_device_id_{}".format(sku),
        headers = ["ft_device_id.h"],
        mode = "ft",
        sku_config = config["orchestrator_cfg"],
        template = ":ft_device_id.c.tpl",
    )
    for sku, config in EARLGREY_SKUS.items()
]

[
    opentitan_binary(
        name = "sram_ft_individualize_{}{}".format(sku, variant),
        testonly = True,
        srcs = ["sram_ft_individualize.c"],
        exec_env = {
            "//hw/top_earlgrey:fpga_cw310_rom_with_fake_keys": None,
            "//hw/top_earlgrey:fpga_cw340_rom_with_fake_keys": None,
            "//hw/top_earlgrey:silicon_creator": None,
            "//hw/top_earlgrey:sim_dv": None,
        },
        kind = "ram",
        linker_script = "//sw/device/silicon_creator/manuf/lib:sram_program_linker_script",
        local_defines = defines,
        deps = [
            ":flash_info_permissions",
            ":ft_device_id_{}_library".format(sku),
            "//hw/top:ast_c_regs",
            "//hw/top_earlgrey/sw/autogen:top_earlgrey",
            "//sw/device/lib/arch:device",
            "//sw/device/lib/base:abs_mmio",
            "//sw/device/lib/base:macros",
            "//sw/device/lib/crypto/drivers:entropy",
            "//sw/device/lib/dif:flash_ctrl",
            "//sw/device/lib/dif:gpio",
            "//sw/device/lib/dif:otp_ctrl",
            "//sw/device/lib/dif:pinmux",
            "//sw/device/lib/runtime:print",
            "//sw/device/lib/testing:pinmux_testutils",
            "//sw/device/lib/testing/json:provisioning_data",
            "//sw/device/lib/testing/test_framework:check",
            "//sw/device/lib/testing/test_framework:ottf_console",
            "//sw/device/lib/testing/test_framework:ottf_test_config",
            "//sw/device/lib/testing/test_framework:status",
            "//sw/device/lib/testing/test_framework:ujson_ottf",
            "//sw/device/silicon_creator/manuf/lib:individualize",
            "//sw/device/silicon_creator/manuf/lib:otp_fields",
            "//sw/device/silicon_creator/manuf/lib:sram_start",
            "//sw/device/silicon_creator/manuf/lib:individualize_sw_cfg_{}".format(config["otp"]),
        ],
    )
    for sku, config in EARLGREY_SKUS.items()
    for variant, defines in {
        "": [],
        "_ate": ["ATE=1"],
    }.items()
]

filegroup(
    name = "sram_ft_individualize_all",
    testonly = True,
    srcs = [
        ":sram_ft_individualize_{}{}".format(sku, variant)
        for sku in EARLGREY_SKUS.keys()
        for variant in [
            "",
            "_ate",
        ]
    ],
)

cc_library(
    name = "personalize_ext",
    hdrs = ["personalize_ext.h"],
    deps = [
        "//sw/device/lib/base:status",
        "//sw/device/lib/dif:flash_ctrl",
        "//sw/device/lib/testing/json:provisioning_data",
        "//sw/device/silicon_creator/lib/cert",
        "//sw/device/silicon_creator/lib/sigverify:ecdsa_p256_key",
    ],
)

cc_library(
    name = "tpm_perso_fw_ext",
    srcs = ["tpm_personalize_ext.c"],
    deps = [
        ":personalize_ext",
        "//sw/device/lib/crypto/drivers:entropy",
        "//sw/device/lib/dif:flash_ctrl",
        "//sw/device/lib/runtime:print",
        "//sw/device/lib/testing/test_framework:status",
        "//sw/device/lib/testing/test_framework:ujson_ottf",
        "//sw/device/silicon_creator/lib:attestation",
        "//sw/device/silicon_creator/lib:otbn_boot_services",
        "//sw/device/silicon_creator/lib/cert",
        "//sw/device/silicon_creator/lib/cert:tpm",
        "//sw/device/silicon_creator/lib/cert:tpm_ek_template_library",
        "//sw/device/silicon_creator/lib/drivers:flash_ctrl",
        "//sw/device/silicon_creator/lib/drivers:hmac",
        "//sw/device/silicon_creator/manuf/base:perso_tlv_data",
        "//sw/device/silicon_creator/manuf/lib:flash_info_fields",
        "//sw/device/silicon_creator/manuf/lib:personalize",
    ],
)

cc_library(
    name = "perso_tlv_data",
    srcs = ["perso_tlv_data.c"],
    deps = [
        ":perso_tlv_headers",
        "//sw/device/silicon_creator/lib:error",
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
        "//sw/device/lib/testing/json:provisioning_data",
        "//sw/device/silicon_creator/lib:error",
        "//sw/device/silicon_creator/lib/cert",
    ],
)

manifest(d = {
    "name": "manifest_perso",
    "identifier": hex(CONST.ROM_EXT),
    "manuf_state_creator": hex(CONST.MANUF_STATE.PERSO_INITIAL),
    "visibility": ["//visibility:private"],
    "version_major": ROM_EXT_VERSION.MAJOR,
    "version_minor": ROM_EXT_VERSION.MINOR,
    "security_version": ROM_EXT_VERSION.SECURITY,
})

[
    opentitan_binary(
        name = "ft_personalize_{}".format(sku),
        testonly = True,
        srcs = ["ft_personalize.c"],
        ecdsa_key = {"//sw/device/silicon_creator/rom/keys/fake/ecdsa:prod_key_0_ecdsa_p256": "prod_key_0"},
        exec_env = {
            "//hw/top_earlgrey:fpga_cw310_rom_with_fake_keys": None,
            "//hw/top_earlgrey:fpga_cw340_rom_with_fake_keys": None,
            "//hw/top_earlgrey:silicon_creator": None,
        },
        linker_script = "//sw/device/lib/testing/test_framework:ottf_ld_silicon_creator_slot_a",
        manifest = ":manifest_perso",
        spx_key = {"//sw/device/silicon_creator/rom/keys/fake/spx:prod_key_0_spx": "prod_key_0"},
        deps = [
            ":flash_info_permissions",
            ":perso_tlv_data",
            ":personalize_ext",
            "//hw/top:otp_ctrl_c_regs",
            "//sw/device/lib/crypto/drivers:entropy",
            "//sw/device/lib/dif:flash_ctrl",
            "//sw/device/lib/dif:gpio",
            "//sw/device/lib/dif:lc_ctrl",
            "//sw/device/lib/dif:otp_ctrl",
            "//sw/device/lib/dif:pinmux",
            "//sw/device/lib/dif:rstmgr",
            "//sw/device/lib/runtime:log",
            "//sw/device/lib/testing:flash_ctrl_testutils",
            "//sw/device/lib/testing:lc_ctrl_testutils",
            "//sw/device/lib/testing:otp_ctrl_testutils",
            "//sw/device/lib/testing:pinmux_testutils",
            "//sw/device/lib/testing:rstmgr_testutils",
            "//sw/device/lib/testing/json:provisioning_data",
            "//sw/device/lib/testing/test_framework:check",
            "//sw/device/lib/testing/test_framework:ottf_main",
            "//sw/device/lib/testing/test_framework:status",
            "//sw/device/lib/testing/test_framework:ujson_ottf",
            "//sw/device/silicon_creator/lib:attestation",
            "//sw/device/silicon_creator/lib:boot_data",
            "//sw/device/silicon_creator/lib:otbn_boot_services",
            "//sw/device/silicon_creator/lib/base:chip",
            "//sw/device/silicon_creator/lib/base:util",
            "//sw/device/silicon_creator/lib/cert",
            "//sw/device/silicon_creator/lib/cert:cdi_0_template_library",
            "//sw/device/silicon_creator/lib/cert:cdi_1_template_library",
            "//sw/device/silicon_creator/lib/cert:uds_template_library",
            "//sw/device/silicon_creator/lib/drivers:flash_ctrl",
            "//sw/device/silicon_creator/lib/drivers:hmac",
            "//sw/device/silicon_creator/lib/drivers:keymgr",
            "//sw/device/silicon_creator/lib/drivers:kmac",
            "//sw/device/silicon_creator/lib/drivers:rstmgr",
            "//sw/device/silicon_creator/lib/drivers:watchdog",
            "//sw/device/silicon_creator/lib/ownership:owner_block",
            "//sw/device/silicon_creator/lib/ownership:ownership_key",
            "//sw/device/silicon_creator/manuf/lib:flash_info_fields",
            "//sw/device/silicon_creator/manuf/lib:individualize_sw_cfg_{}".format(config["otp"]),
            "//sw/device/silicon_creator/manuf/lib:personalize",
        ] + config["dice_libs"] + config["device_ext_libs"] + config.get("ownership_libs", []),
    )
    for sku, config in EARLGREY_SKUS.items()
]

[
    opentitan_binary_assemble(
        name = "ft_fw_bundle_{}".format(sku),
        testonly = True,
        bins = {
            # Use a pre-compiled perso binary if the SKU defines it,
            # else use the label of the opentitan_binary for the SKU.
            config.get(
                "perso_bin",
                ":ft_personalize_{}".format(sku),
            ): SLOTS["a"],
            config["rom_ext"]: SLOTS["b"],
            config["owner_fw"]: OWNER_SLOTS["b"],
        },
        exec_env = [
            "//hw/top_earlgrey:fpga_cw310_rom_with_fake_keys",
            "//hw/top_earlgrey:fpga_cw340_rom_with_fake_keys",
            "//hw/top_earlgrey:silicon_creator",
        ],
    )
    for sku, config in EARLGREY_SKUS.items()
]

filegroup(
    name = "ft_personalize_all",
    testonly = True,
    # The depset(...).to_list() syntax removes duplicate bazel targets. Some
    # SKUs have duplicate "staging" versions that are identical to their
    # production counterparts, including the perso binaries used, except for CA
    # keys, so we need to remove duplicates.
    srcs = depset([
                      # Select pre-signed / checked-in perso binaries over ones
                      # built on the fly with fake keys if a pre-signed one
                      # exists.
                      config.get(
                          "perso_bin",
                          ":ft_personalize_{}".format(sku),
                      )
                      for sku, config in EARLGREY_SKUS.items()
                  ] +
                  [
                      ":ft_fw_bundle_{}".format(sku)
                      for sku in EARLGREY_SKUS.keys()
                  ]).to_list(),
)

[
    offline_presigning_artifacts(
        name = "provisioning_{}".format(sku),
        testonly = True,
        srcs = [":ft_personalize_{}".format(sku)],
        ecdsa_key = data["ecdsa_key"],
        manifest = ":manifest_perso",
        spx_key = data["spx_key"],
        tags = ["manual"],
    )
    for sku, data in EARLGREY_SKUS.items()
    if not disqualified_for_signing(sku, data)
]

pkg_tar(
    name = "digests",
    testonly = True,
    srcs = [
        ":provisioning_{}".format(sku)
        for sku, data in EARLGREY_SKUS.items()
        if not disqualified_for_signing(sku, data)
    ],
    mode = "0644",
    tags = ["manual"],
)

offline_signature_attach(
    name = "signed",
    testonly = True,
    srcs = [
        ":provisioning_{}".format(sku)
        for sku, data in EARLGREY_SKUS.items()
        if not disqualified_for_signing(sku, data)
    ],
    ecdsa_signatures = [
        "//sw/device/silicon_creator/manuf/base/signatures:ecdsa_signatures",
    ] + depset([
        "{}:ecdsa_signatures".format(data["signature_prefix"])
        for sku, data in EARLGREY_SKUS.items()
        if data["signature_prefix"] and not disqualified_for_signing(sku, data)
    ]).to_list(),
    spx_signatures = [
        "//sw/device/silicon_creator/manuf/base/signatures:spx_signatures",
    ] + depset([
        "{}:spx_signatures".format(data["signature_prefix"])
        for sku, data in EARLGREY_SKUS.items()
        if data["signature_prefix"] and not disqualified_for_signing(sku, data)
    ]).to_list(),
    tags = ["manual"],
)
