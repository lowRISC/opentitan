# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load(
    "//rules/opentitan:defs.bzl",
    "fpga_params",
    "opentitan_test",
)

package(default_visibility = ["//visibility:public"])

opentitan_test(
    name = "xmodem_protocol",
    exec_env = {
        "//hw/top_earlgrey:fpga_hyper310_rom_ext": None,
        "//hw/top_earlgrey:fpga_cw340_rom_ext": None,
    },
    fpga = fpga_params(
        assemble = "",
        binaries = {
            "//sw/device/silicon_creator/rom_ext/e2e/rescue:boot_test_slot_a": "boot_test",
        },
        test_cmd = """
            --bootstrap={rom_ext}
            --firmware={boot_test}
        """,
        test_harness = "//sw/host/tests/rescue:xmodem_protocol",
        testopt_bootstrap = "False",
        testopt_clear_after_test = "True",
        testopt_clear_before_test = "True",
    ),
)

opentitan_test(
    name = "usbdfu_protocol",
    exec_env = {
        "//hw/top_earlgrey:fpga_hyper310_rom_ext": None,
        "//hw/top_earlgrey:fpga_cw340_rom_ext": None,
    },
    fpga = fpga_params(
        assemble = "",
        binaries = {
            "//sw/device/silicon_creator/rom_ext/e2e/rescue:boot_test_slot_a": "boot_test",
        },
        rom_ext = "//sw/device/silicon_creator/rom_ext:rom_ext_usbdfu",
        test_cmd = """
            --bootstrap={rom_ext}
            --firmware={boot_test}
            --trigger=strap
            --value=3
        """,
        test_harness = "//sw/host/tests/rescue:usbdfu_protocol",
        testopt_bootstrap = "False",
        testopt_clear_after_test = "True",
        testopt_clear_before_test = "True",
    ),
)
