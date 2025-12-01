# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

package(default_visibility = ["//visibility:public"])

load("@//rules:signing.bzl", "offline_presigning_artifacts", "offline_signature_attach")
load(
    "//rules/opentitan:defs.bzl",
    "opentitan_binary",
    "opentitan_test",
    "silicon_params",
)

# Building a wrongly signed BL0 binary for testing the secure boot
opentitan_binary(
    name = "bl0_firmware",
    testonly = True,
    # This can be any other source of the pentest framework
    srcs = ["//sw/device/tests/penetrationtests/firmware:firmware_cryptolib_fi_sym.c"],
    exec_env = {
        "//hw/top_earlgrey:fpga_cw340_rom_ext": None,
    },
    deps = [
        "//sw/device/tests/penetrationtests/firmware/sca:trigger_sca",
        "//sw/device/tests/penetrationtests/firmware/fi:cryptolib_fi_sym",
        "//sw/device/tests/penetrationtests/firmware/lib:extclk_sca_fi",
        "//sw/device/tests/penetrationtests/firmware/lib:pentest_lib",
        "//sw/device/lib/base:csr",
        "//sw/device/lib/base:status",
        "//sw/device/lib/crypto/drivers:entropy",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/lib/testing/test_framework:ujson_ottf",
        "//sw/device/lib/ujson",

        # Include all JSON commands.
        "//sw/device/tests/penetrationtests/json:commands",
    ],
)

offline_presigning_artifacts(
    name = "non_signed_firmware",
    testonly = True,
    srcs = [":bl0_firmware"],
    ecdsa_key = {"//sw/device/silicon_creator/lib/ownership/keys/fake:app_prod_ecdsa": "prod_key_0"},
    manifest = "//sw/device/silicon_owner:manifest",
    spx_key = {},
    tags = ["manual"],
)

offline_signature_attach(
    name = "wrong_signed_firmware",
    testonly = True,
    srcs = [":non_signed_firmware"],
    # We provide a wrong signature
    ecdsa_signatures = ["bl0_firmware_fpga_cw340_rom_ext.ecdsa_sig"],
    spx_signatures = [],
    tags = ["manual"],
)
