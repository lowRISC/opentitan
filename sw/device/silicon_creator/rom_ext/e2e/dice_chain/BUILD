# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load(
    "//rules/opentitan:cc.bzl",
    "opentitan_binary_assemble",
)
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
        deps = [
            "//sw/device/lib/base:status",
            "//sw/device/lib/runtime:log",
            "//sw/device/lib/testing/test_framework:check",
            "//sw/device/lib/testing/test_framework:ottf_console",
            "//sw/device/lib/testing/test_framework:ottf_main",
            "//sw/device/silicon_creator/lib:attestation",
            "//sw/device/silicon_creator/lib:otbn_boot_services",
            "//sw/device/silicon_creator/lib/cert",
            "//sw/device/silicon_creator/lib/cert:dice_chain",
            "//sw/device/silicon_creator/lib/cert:dice_keys",
            "//sw/device/silicon_creator/lib/drivers:retention_sram",
            "//sw/device/silicon_creator/lib/drivers:rstmgr",
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
