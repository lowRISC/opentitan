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
    "qemu_params",
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
            "//hw/top_earlgrey:sim_qemu_rom_ext": None,
        },
        fpga = fpga_params(
            exit_failure = "Rebooting[\\s\\S]*CDI_1 certificate not valid[\\s\\S]*Rebooted",
            exit_success = "Rebooted\r\n",
            rom_ext = "//sw/device/silicon_creator/rom_ext:rom_ext_{}_slot_a".format(variation),
        ),
        qemu = qemu_params(
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
        "//hw/top_earlgrey:sim_qemu_rom_ext": None,
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
            "//hw/top_earlgrey:sim_qemu_rom_with_fake_keys",
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
            "//hw/top_earlgrey:sim_qemu_rom_with_fake_keys": None,
        },
        fpga = fpga_params(
            binaries = {
                ":dice_{}_rom_ext_owner_bundle".format(tc["second"]): "second",
                ":dice_{}_rom_ext_owner_bundle".format(tc["first"]): "firmware",
            },
            otp = "//sw/device/silicon_creator/rom_ext/e2e:otp_img_secret2_locked_rma",
            test_cmd = """
                --second-bootstrap={second}
            """,
            test_harness = "//sw/host/tests/rom_ext/e2e_variation_interop",
            testopt_clear_before_test = "True",
        ),
        qemu = qemu_params(
            binaries = {
                ":dice_{}_rom_ext_owner_bundle".format(tc["second"]): "second",
                ":dice_{}_rom_ext_owner_bundle".format(tc["first"]): "firmware",
            },
            otp = "//sw/device/silicon_creator/rom_ext/e2e:otp_img_secret2_locked_rma",
            test_cmd = """
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
        "//hw/top_earlgrey:sim_qemu_rom_with_fake_keys",
    ],
    deps = [
        "//hw/top_earlgrey/ip_autogen/flash_ctrl:flash_ctrl_c_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:status",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:ottf_alerts",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/lib/drivers:flash_ctrl",
        "//sw/device/silicon_creator/lib/drivers:hmac",
    ],
)

CORRUPTED_DIGEST_TEST_CMDS = """
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
"""

opentitan_test(
    name = "corrupted_digest_test",
    srcs = ["//sw/device/silicon_creator/rom_ext/e2e/verified_boot:boot_test"],
    exec_env = {
        "//hw/top_earlgrey:fpga_cw340_rom_ext": None,
        "//hw/top_earlgrey:sim_qemu_rom_ext": None,
    },
    fpga = fpga_params(
        binaries = {
            ":modify_digest": "modify_digest",
        },
        test_cmd = CORRUPTED_DIGEST_TEST_CMDS,
        testopt_bootstrap = "False",
        testopt_clear_before_test = "True",
    ),
    qemu = qemu_params(
        binaries = {
            ":modify_digest": "modify_digest",
        },
        test_cmd = ("""
            --exec="transport init"
        """ + CORRUPTED_DIGEST_TEST_CMDS),
    ),
    deps = [
        "//sw/device/lib/base:status",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/lib:boot_log",
        "//sw/device/silicon_creator/lib/drivers:retention_sram",
    ],
)

DEBUG_MODE_TESTCASES = [
    {
        "name": "off",
        "key": {"//sw/device/silicon_creator/lib/ownership/keys/fake:ecdsa_keyset": "app_prod_0"},
        "defines": ["TEST_EXPECT_DEBUG_OFF=1"],
    },
    {
        "name": "on",
        "key": {"//sw/device/silicon_creator/lib/ownership/keys/fake:ecdsa_keyset": "app_test_0"},
        "defines": ["TEST_EXPECT_DEBUG_ON=1"],
    },
]

[
    opentitan_test(
        name = "debug_mode_{}_{}_test".format(
            testcase["name"],
            variation,
        ),
        srcs = ["debug_mode_test.c"],
        defines = testcase["defines"],
        ecdsa_key = testcase["key"],
        exec_env = {
            "//hw/top_earlgrey:fpga_cw310_rom_ext": None,
            "//hw/top_earlgrey:fpga_cw340_rom_ext": None,
            "//hw/top_earlgrey:sim_qemu_rom_ext": None,
        },
        fpga = fpga_params(
            rom_ext = "//sw/device/silicon_creator/rom_ext:rom_ext_{}_slot_a".format(variation),
        ),
        qemu = qemu_params(
            rom_ext = "//sw/device/silicon_creator/rom_ext:rom_ext_{}_slot_a".format(variation),
        ),
        deps = [
            "//sw/device/lib/base:status",
            "//sw/device/lib/runtime:log",
            "//sw/device/lib/testing/test_framework:check",
            "//sw/device/lib/testing/test_framework:ottf_main",
            "//sw/device/silicon_creator/lib/drivers:flash_ctrl",
            "//sw/device/silicon_creator/manuf/base:perso_tlv_data",
        ],
    )
    for testcase in DEBUG_MODE_TESTCASES
    for variation in ROM_EXT_VARIATIONS.keys()
]

[
    opentitan_binary(
        name = "cdi1_key_sign_for_assemble_{}".format(i),
        testonly = True,
        srcs = ["cdi1_key_sign_test.c"],
        exec_env = [
            "//hw/top_earlgrey:fpga_cw310_rom_ext",
            "//hw/top_earlgrey:fpga_cw340_rom_ext",
        ],
        linker_script = "//sw/device/lib/testing/test_framework:ottf_ld_silicon_owner_slot_a",
        local_defines = [
            "EMPTY_TEST_MSG=\"Test Owner FW - {}.\"".format(i if i < 2 else 0),
        ],
        manifest = ":owner_manifest",
        deps = [
            "//sw/device/lib/base:status",
            "//sw/device/lib/runtime:log",
            "//sw/device/lib/testing/test_framework:check",
            "//sw/device/lib/testing/test_framework:ottf_main",
        ],
    )
    for i in range(3)
]

[
    opentitan_binary_assemble(
        name = "cdi1_key_sign_rom_ext_owner_bundle_{}".format(i),
        testonly = True,
        bins = {
            "//sw/device/silicon_creator/rom_ext:rom_ext_dice_x509_slot_a": SLOTS["a"],
            ":cdi1_key_sign_for_assemble_{}".format(i): OWNER_SLOTS["a"],
        },
        exec_env = [
            "//hw/top_earlgrey:fpga_cw310_rom_with_fake_keys",
            "//hw/top_earlgrey:fpga_cw340_rom_with_fake_keys",
        ],
    )
    for i in range(3)
]

opentitan_test(
    name = "cdi1_key_sign_test",
    exec_env = {
        "//hw/top_earlgrey:fpga_cw310_rom_with_fake_keys": None,
        "//hw/top_earlgrey:fpga_cw340_rom_with_fake_keys": None,
    },
    fpga = fpga_params(
        binaries = {
            ":cdi1_key_sign_rom_ext_owner_bundle_0": "firmware",
            ":cdi1_key_sign_rom_ext_owner_bundle_1": "second",
            ":cdi1_key_sign_rom_ext_owner_bundle_2": "third",
        },
        otp = "//sw/device/silicon_creator/rom_ext/e2e:otp_img_secret2_locked_rma",
        test_cmd = """
            --bootstrap={firmware}
            --second-bootstrap={second}
            --third-bootstrap={third}
        """,
        test_harness = "//sw/host/tests/rom_ext/cdi1_key_sign",
    ),
)
