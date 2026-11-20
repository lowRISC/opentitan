# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_rust//rust:defs.bzl", "rust_binary")
load("//hw/top_earlgrey:defs.bzl", "EARLGREY_MLDSA_SLOTS")
load("//rules:certificates.bzl", "certificate_template")
load("//rules:const.bzl", "CONST", "hex")
load("//rules:linker.bzl", "ld_library")
load("//rules:manifest.bzl", "manifest")
load("//rules/opentitan:cc.bzl", "opentitan_binary_assemble")
load(
    "//rules/opentitan:defs.bzl",
    "fpga_params",
    "opentitan_binary",
    "opentitan_test",
    "qemu_params",
)

package(default_visibility = ["//visibility:public"])

certificate_template(
    name = "uds_mldsa_template",
    template = "uds_mldsa.hjson",
)

ld_library(
    name = "ld_slot_virtual",
    script = "uds_instantiate_slot_virtual.ld",
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey_memory",
        "//sw/device:info_sections",
        "//sw/device/lib/coverage:coverage_sections",
        "//sw/device/silicon_creator/lib/base:static_critical_sections",
        "//sw/device/silicon_creator/lib/base:static_dice_sections",
    ],
)

manifest({
    "name": "manifest",
    "identifier": hex(CONST.OWNER),
    "manifest_version_major": hex(CONST.MANIFEST_VERSION_MAJOR_3),
    "manifest_version_minor": hex(0),
})

opentitan_binary(
    name = "uds_instantiate",
    testonly = True,
    srcs = [
        "uds_instantiate.c",
        "//sw/device/silicon_owner/bare_metal:bare_metal_start",
    ],
    exec_env = [
        "//hw/top_earlgrey:fpga_hyper310_rom_ext",
        "//hw/top_earlgrey:fpga_cw340_rom_ext",
        "//hw/top_earlgrey:silicon_owner_sival_rom_ext",
        "//hw/top_earlgrey:sim_qemu_rom_ext",
        # TODO: run on a GB chip
        #"@provisioning_exts//shared/exec_env:silicon_owner_gb_rom_ext",
    ],
    linker_script = ":ld_slot_virtual",
    manifest = ":manifest",
    slot_spec = EARLGREY_MLDSA_SLOTS,
    deps = [
        ":uds_mldsa_template_library",
        "//hw/top_earlgrey/ip_autogen/flash_ctrl:flash_ctrl_c_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:crc32",
        "//sw/device/lib/base:csr",
        "//sw/device/lib/base:hardened",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:multibits",
        "//sw/device/lib/base:status",
        "//sw/device/lib/crt",
        "//sw/device/lib/crypto/impl:config",
        "//sw/device/lib/crypto/impl:cryptolib_build_info",
        "//sw/device/lib/crypto/impl:ecc_p256",
        "//sw/device/lib/crypto/impl:integrity",
        "//sw/device/lib/crypto/impl:key_transport",
        "//sw/device/lib/crypto/impl:sha2",
        "//sw/device/lib/crypto/include:datatypes",
        "//sw/device/lib/runtime:hart",
        "//sw/device/silicon_creator/lib:attestation",
        "//sw/device/silicon_creator/lib:dbg_print",
        "//sw/device/silicon_creator/lib:error",
        "//sw/device/silicon_creator/lib:manifest_def",
        "//sw/device/silicon_creator/lib/base:sec_mmio",
        "//sw/device/silicon_creator/lib/base:static_critical",
        "//sw/device/silicon_creator/lib/base:static_dice_cdi_0",
        "//sw/device/silicon_creator/lib/base:static_dice_mldsa_cdi",
        "//sw/device/silicon_creator/lib/base:util",
        "//sw/device/silicon_creator/lib/cert",
        "//sw/device/silicon_creator/lib/cert:dice_keys",
        "//sw/device/silicon_creator/lib/cert:ram_msg",
        "//sw/device/silicon_creator/lib/drivers:flash_ctrl",
        "//sw/device/silicon_creator/lib/drivers:retention_sram",
        "//sw/device/silicon_creator/lib/drivers:rstmgr",
        "//sw/device/silicon_creator/lib/drivers:uart",
        "//sw/device/silicon_creator/lib/drivers:watchdog",
        "//sw/device/silicon_creator/manuf/base:perso_tlv_data",
    ],
)

opentitan_binary(
    name = "provision_factory_uds",
    testonly = True,
    srcs = ["provision_factory_uds.c"],
    exec_env = [
        "//hw/top_earlgrey:fpga_hyper310_rom_with_fake_keys",
        "//hw/top_earlgrey:fpga_cw340_rom_with_fake_keys",
        "//hw/top_earlgrey:sim_qemu_rom_with_fake_keys",
    ],
    deps = [
        "//hw/top_earlgrey/ip_autogen/flash_ctrl:flash_ctrl_c_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:status",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:ottf_alerts",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/lib:otbn_boot_services",
        "//sw/device/silicon_creator/lib/base:static_dice_cdi_0",
        "//sw/device/silicon_creator/lib/base:util",
        "//sw/device/silicon_creator/lib/cert",
        "//sw/device/silicon_creator/lib/cert:dice_api",
        "//sw/device/silicon_creator/lib/cert:dice_chain",
        "//sw/device/silicon_creator/lib/cert:dice_keys",
        "//sw/device/silicon_creator/lib/cert:dice_uds_cert_build",
        "//sw/device/silicon_creator/lib/cert:template",
        "//sw/device/silicon_creator/lib/cert:uds_template_library",
        "//sw/device/silicon_creator/lib/drivers:flash_ctrl",
        "//sw/device/silicon_creator/lib/drivers:hmac",
        "//sw/device/silicon_creator/lib/sigverify:ecdsa_p256_key",
        "//sw/device/silicon_creator/manuf/base:perso_tlv_data",
    ],
)

opentitan_binary_assemble(
    name = "uds_instantiate_mldsa_bundle",
    testonly = True,
    bins = {
        "//sw/device/silicon_creator/rom_ext:rom_ext_dice_mldsa_slot_a": "{rom_ext_slot_a}",
        ":uds_instantiate": "{owner_slot_b}",
    },
    exec_env = [
        "//hw/top_earlgrey:fpga_hyper310_rom_ext",
        "//hw/top_earlgrey:fpga_cw340_rom_ext",
        "//hw/top_earlgrey:sim_qemu_rom_ext",
    ],
    slot_spec = EARLGREY_MLDSA_SLOTS,
)

rust_binary(
    name = "uds_instantiate_test_harness",
    testonly = True,
    srcs = ["uds_instantiate_test.rs"],
    data = ["@openssl"],
    edition = "2024",
    deps = [
        "//sw/host/opentitanlib",
        "//sw/host/ot_certs",
        "@crate_index//:anyhow",
        "@crate_index//:base64ct",
        "@crate_index//:clap",
        "@crate_index//:hex",
        "@crate_index//:humantime",
        "@crate_index//:log",
        "@crate_index//:num-bigint-dig",
        "@crate_index//:regex",
        "@crate_index//:tempfile",
        "@rules_rust//rust/runfiles",
    ],
)

opentitan_test(
    name = "uds_instantiate_test",
    exec_env = {
        "//hw/top_earlgrey:fpga_hyper310_rom_ext": None,
        "//hw/top_earlgrey:fpga_cw340_rom_ext": None,
        "//hw/top_earlgrey:sim_qemu_rom_ext": None,
    },
    fpga = fpga_params(
        assemble = "{rom_ext}@{rom_ext_slot_a} {firmware}@{owner_slot_b}",
        binaries = {
            ":uds_instantiate": "firmware",
        },
        rom_ext = "//sw/device/silicon_creator/rom_ext:rom_ext_dice_mldsa_slot_a",
        test_cmd = """
            --bootstrap={firmware}
            --timeout=45s
        """,
        test_harness = ":uds_instantiate_test_harness",
        testopt_bootstrap = "False",
        testopt_clear_before_test = "True",
    ),
    qemu = qemu_params(
        assemble = "{rom_ext}@{rom_ext_slot_a} {firmware}@{owner_slot_b}",
        binaries = {
            ":uds_instantiate": "firmware",
        },
        rom_ext = "//sw/device/silicon_creator/rom_ext:rom_ext_dice_mldsa_slot_a",
        test_cmd = """
            --bootstrap={firmware}
            --timeout=90s
        """,
        test_harness = ":uds_instantiate_test_harness",
    ),
    slot_spec = EARLGREY_MLDSA_SLOTS,
)

opentitan_test(
    name = "uds_instantiate_tcb_copy_test",
    exec_env = {
        "//hw/top_earlgrey:fpga_hyper310_rom_with_fake_keys": None,
        "//hw/top_earlgrey:fpga_cw340_rom_with_fake_keys": None,
        "//hw/top_earlgrey:sim_qemu_rom_with_fake_keys": None,
    },
    fpga = fpga_params(
        binaries = {
            ":provision_factory_uds": "firmware",
            ":uds_instantiate_mldsa_bundle": "second",
        },
        otp = "//sw/device/silicon_creator/rom_ext/e2e:otp_img_secret2_locked_rma",
        test_cmd = """
            --second-bootstrap={second}
            --expect-factory-uds
            --timeout=45s
        """,
        test_harness = ":uds_instantiate_test_harness",
        testopt_clear_before_test = "True",
    ),
    qemu = qemu_params(
        binaries = {
            ":provision_factory_uds": "firmware",
            ":uds_instantiate_mldsa_bundle": "second",
        },
        otp = "//sw/device/silicon_creator/rom_ext/e2e:otp_img_secret2_locked_rma",
        test_cmd = """
            --bootstrap={firmware}
            --second-bootstrap={second}
            --expect-factory-uds
            --timeout=90s
        """,
        test_harness = ":uds_instantiate_test_harness",
    ),
)
