# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

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
    "//sw/device/silicon_creator/rom/e2e:defs.bzl",
    "SLOTS",
)
load(
    "//sw/device/silicon_creator/rom_ext:defs.bzl",
    "ROM_EXT_VARIATIONS",
)
load(
    "//sw/device/silicon_creator/rom_ext/e2e:defs.bzl",
    "OWNER_SLOTS",
)

package(default_visibility = ["//visibility:public"])

[
    opentitan_test(
        name = "no_refresh_{}_test".format(variation),
        srcs = ["no_refresh_test.c"],
        exec_env = {
            "//hw/top_earlgrey:fpga_cw310_rom_ext": None,
            "//hw/top_earlgrey:fpga_cw340_rom_ext": None,
        },
        fpga = fpga_params(
            exit_failure = "Rebooting[\\s\\S]*CDI_1 certificate not valid[\\s\\S]*Rebooted",
            exit_success = "Rebooted\r\n",
            rom_ext = "//sw/device/silicon_creator/rom_ext:rom_ext_{}_slot_a".format(variation),
        ),
        deps = [
            "//sw/device/lib/base:status",
            "//sw/device/lib/runtime:log",
            "//sw/device/lib/testing/test_framework:check",
            "//sw/device/lib/testing/test_framework:ottf_main",
            "//sw/device/silicon_creator/lib/drivers:retention_sram",
            "//sw/device/silicon_creator/lib/drivers:rstmgr",
        ],
    )
    for variation in ROM_EXT_VARIATIONS.keys()
]

manifest({
    "name": "owner_manifest",
    "identifier": hex(CONST.OWNER),
    "visibility": ["//visibility:private"],
})

opentitan_binary(
    name = "print_certs_for_assemble",
    testonly = True,
    srcs = ["//sw/device/silicon_creator/rom_ext/e2e/attestation:print_certs.c"],
    exec_env = {
        "//hw/top_earlgrey:fpga_cw310_rom_ext": None,
        "//hw/top_earlgrey:fpga_cw340_rom_ext": None,
    },
    linker_script = "//sw/device/lib/testing/test_framework:ottf_ld_silicon_owner_slot_a",
    manifest = ":owner_manifest",
    deps = [
        "//sw/device/lib/base:status",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/runtime:print",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/lib/drivers:flash_ctrl",
        "//sw/device/silicon_creator/manuf/base:perso_tlv_data",
    ],
)

[
    opentitan_binary_assemble(
        name = "{}_rom_ext_owner_bundle".format(variation),
        testonly = True,
        bins = {
            "//sw/device/silicon_creator/rom_ext:rom_ext_{}_slot_a".format(variation): SLOTS["a"],
            ":print_certs_for_assemble": OWNER_SLOTS["a"],
        },
        exec_env = [
            "//hw/top_earlgrey:fpga_cw310_rom_with_fake_keys",
            "//hw/top_earlgrey:fpga_cw340_rom_with_fake_keys",
        ],
    )
    for variation in ROM_EXT_VARIATIONS.keys()
]

_VARIATION_INTEROP_TEST_CASES = [
    {
        "first": "x509",
        "second": "cwt",
    },
    {
        "first": "cwt",
        "second": "x509",
    },
]

[
    opentitan_test(
        name = "variation_interop_{}_first_test".format(tc["first"]),
        exec_env = {
            "//hw/top_earlgrey:fpga_cw310_rom_with_fake_keys": None,
            "//hw/top_earlgrey:fpga_cw340_rom_with_fake_keys": None,
        },
        fpga = fpga_params(
            binaries = {
                ":dice_{}_rom_ext_owner_bundle".format(tc["second"]): "second",
                ":dice_{}_rom_ext_owner_bundle".format(tc["first"]): "firmware",
            },
            otp = "//sw/device/silicon_creator/rom_ext/e2e:otp_img_secret2_locked_rma",
            test_cmd = """
                --clear-bitstream
                --bootstrap={firmware}
                --second-bootstrap={second}
            """,
            test_harness = "//sw/host/tests/rom_ext/e2e_variation_interop",
        ),
    )
    for tc in _VARIATION_INTEROP_TEST_CASES
]

test_suite(
    name = "variation_interop_tests",
    tags = ["manual"],
    tests = [
        "variation_interop_{}_first_test".format(
            tc["first"],
        )
        for tc in _VARIATION_INTEROP_TEST_CASES
    ],
)

opentitan_binary(
    name = "modify_digest",
    testonly = True,
    srcs = ["modify_digest.c"],
    exec_env = [
        "//hw/top_earlgrey:fpga_cw340_rom_with_fake_keys",
    ],
    deps = [
        "//hw/top:flash_ctrl_c_regs",
        "//sw/device/lib/base:status",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/lib/drivers:flash_ctrl",
        "//sw/device/silicon_creator/lib/drivers:hmac",
    ],
)

opentitan_test(
    name = "corrupted_digest_test",
    srcs = ["//sw/device/silicon_creator/rom_ext/e2e/verified_boot:boot_test"],
    exec_env = {
        "//hw/top_earlgrey:fpga_cw340_rom_ext": None,
    },
    fpga = fpga_params(
        binaries = {
            ":modify_digest": "modify_digest",
        },
        test_cmd = """
            --exec="transport init"
            --exec="fpga clear-bitstream"
            --exec="fpga load-bitstream {bitstream}"
            --exec="no-op --info='##### Prepare CDI cert page'"
            --exec="bootstrap --clear-uart=true {firmware}"
            --exec="console --non-interactive --exit-success='{exit_success}' --exit-failure='{exit_failure}' --timeout=10s"
            --exec="no-op --info='##### Corrupt CDI cert page'"
            --exec="bootstrap --clear-uart=true {modify_digest}"
            --exec="console --non-interactive --exit-success='PASS!' --timeout=10s"
            --exec="bootstrap --clear-uart=true {firmware}"
            --exec="no-op --info='##### Corruption should be detected and reboot'"
            --exec="console --non-interactive --exit-success='BFV:03444303' --exit-failure='{exit_success}' --timeout=10s"
            --exec="no-op --info='##### Corruption fixed in the second boot'"
            --exec="console --non-interactive --exit-success='{exit_success}' --exit-failure='{exit_failure}' --timeout=10s"
            no-op
        """,
    ),
    deps = [
        "//sw/device/lib/base:status",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/lib:boot_log",
        "//sw/device/silicon_creator/lib/drivers:retention_sram",
    ],
)
