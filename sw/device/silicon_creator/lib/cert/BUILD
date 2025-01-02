# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load(
    "//rules:certificates.bzl",
    "certificate_template",
)

package(default_visibility = ["//visibility:public"])

certificate_template(
    name = "generic_template",
    template = "//sw/host/ot_certs:generic_cert",
)

certificate_template(
    name = "example_template",
    template = "//sw/host/ot_certs:example_cert",
)

certificate_template(
    name = "uds_template",
    template = "uds.hjson",
)

certificate_template(
    name = "cdi_0_template",
    template = "cdi_0.hjson",
)

certificate_template(
    name = "cdi_1_template",
    template = "cdi_1.hjson",
)

certificate_template(
    name = "cwt_cose_key_template",
    cert_format = "cwt",
    template = "cwt_cose_key.hjson",
)

certificate_template(
    name = "cwt_dice_chain_entry_payload_template",
    cert_format = "cwt",
    template = "cwt_dice_chain_entry_payload.hjson",
)

certificate_template(
    name = "cwt_dice_chain_entry_input_template",
    cert_format = "cwt",
    template = "cwt_dice_chain_entry_input.hjson",
)

certificate_template(
    name = "cwt_dice_chain_entry_template",
    cert_format = "cwt",
    template = "cwt_dice_chain_entry.hjson",
)

certificate_template(
    name = "tpm_ek_template",
    template = "tpm_ek.hjson",
)

cc_library(
    name = "asn1",
    srcs = ["asn1.c"],
    hdrs = ["asn1.h"],
    deps = [
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:status",
    ],
)

cc_test(
    name = "asn1_unittest",
    srcs = ["asn1_unittest.cc"],
    deps = [
        ":asn1",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "cert",
    srcs = ["cert.c"],
    hdrs = ["cert.h"],
    deps = [
        ":asn1",
        "//hw/top_earlgrey/ip_autogen/flash_ctrl:flash_ctrl_c_regs",
        "//sw/device/lib/base:hardened",
        "//sw/device/silicon_creator/lib:error",
        "//sw/device/silicon_creator/lib/drivers:flash_ctrl",
        "//sw/device/silicon_creator/lib/drivers:hmac",
        "//sw/device/silicon_creator/lib/drivers:keymgr",
        "//sw/device/silicon_creator/lib/sigverify:ecdsa_p256_key",
    ],
)

cc_test(
    name = "cert_unittest",
    srcs = ["cert_unittest.cc"],
    deps = [
        ":cert",
        "//hw/top_earlgrey/ip_autogen/flash_ctrl:flash_ctrl_c_regs",
        "//sw/device/lib/base:hardened",
        "//sw/device/silicon_creator/lib:error",
        "//sw/device/silicon_creator/testing:rom_test",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "dice",
    srcs = ["dice.c"],
    hdrs = ["dice.h"],
    deps = [
        ":cert",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:status",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/silicon_creator/lib:attestation",
        "//sw/device/silicon_creator/lib:otbn_boot_services",
        "//sw/device/silicon_creator/lib/base:util",
        "//sw/device/silicon_creator/lib/cert:cdi_0_template_library",
        "//sw/device/silicon_creator/lib/cert:cdi_1_template_library",
        "//sw/device/silicon_creator/lib/cert:dice_keys",
        "//sw/device/silicon_creator/lib/cert:uds_template_library",
        "//sw/device/silicon_creator/lib/drivers:hmac",
        "//sw/device/silicon_creator/lib/drivers:lifecycle",
        "//sw/device/silicon_creator/lib/sigverify:ecdsa_p256_key",
        "//sw/device/silicon_creator/manuf/base:perso_tlv_data",
        "//sw/device/silicon_creator/manuf/lib:flash_info_fields",
    ],
)

cc_library(
    name = "cbor",
    hdrs = ["cbor.h"],
    deps = [
        "//sw/device/lib/base:status",
        "//sw/device/lib/runtime:log",
        "@open-dice//:cbor_reader_writer",
    ],
)

cc_library(
    name = "cwt_template",
    deps = [
        ":cbor",
        ":cwt_cose_key_template_library",
        ":cwt_dice_chain_entry_input_template_library",
        ":cwt_dice_chain_entry_payload_template_library",
        ":cwt_dice_chain_entry_template_library",
        "//sw/device/lib/base:status",
    ],
)

cc_library(
    name = "dice_cwt",
    srcs = ["dice_cwt.c"],
    hdrs = ["dice.h"],
    deps = [
        ":cbor",
        ":cert",
        ":cwt_template",
        "//hw/ip/otp_ctrl/data:otp_ctrl_c_regs",
        "//sw/device/lib/base:status",
        "//sw/device/silicon_creator/lib:attestation",
        "//sw/device/silicon_creator/lib:otbn_boot_services",
        "//sw/device/silicon_creator/lib/base:util",
        "//sw/device/silicon_creator/lib/cert:dice_keys",
        "//sw/device/silicon_creator/lib/drivers:lifecycle",
        "//sw/device/silicon_creator/manuf/base:perso_tlv_data",
    ],
)

cc_library(
    name = "dice_keys",
    srcs = ["dice_keys.c"],
    hdrs = ["dice_keys.h"],
    deps = [
        "//sw/device/silicon_creator/lib/drivers:keymgr",
        "//sw/device/silicon_creator/manuf/lib:flash_info_fields",
    ],
)

cc_library(
    name = "tpm",
    srcs = ["tpm.c"],
    hdrs = ["tpm.h"],
    deps = [
        ":cert",
        "//sw/device/lib/base:status",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/silicon_creator/lib/cert:tpm_ek_template_library",
        "//sw/device/silicon_creator/lib/drivers:keymgr",
        "//sw/device/silicon_creator/lib/sigverify:ecdsa_p256_key",
        "//sw/device/silicon_creator/manuf/lib:flash_info_fields",
    ],
)

cc_library(
    name = "dice_chain",
    srcs = ["dice_chain.c"],
    hdrs = ["dice_chain.h"],
    deps = [
        "//hw/top_earlgrey/ip_autogen/flash_ctrl:flash_ctrl_c_regs",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/crypto/drivers:entropy",
        "//sw/device/silicon_creator/lib:dbg_print",
        "//sw/device/silicon_creator/lib:keymgr_binding",
        "//sw/device/silicon_creator/lib:manifest",
        "//sw/device/silicon_creator/lib/base:boot_measurements",
        "//sw/device/silicon_creator/lib/base:sec_mmio",
        "//sw/device/silicon_creator/lib/base:util",
        "//sw/device/silicon_creator/lib/cert:cdi_0_template_library",
        "//sw/device/silicon_creator/lib/cert:cdi_1_template_library",
        "//sw/device/silicon_creator/lib/cert:dice",
        "//sw/device/silicon_creator/lib/drivers:flash_ctrl",
        "//sw/device/silicon_creator/lib/drivers:keymgr",
        "//sw/device/silicon_creator/lib/drivers:kmac",
        "//sw/device/silicon_creator/manuf/base:perso_tlv_data",
    ],
)
