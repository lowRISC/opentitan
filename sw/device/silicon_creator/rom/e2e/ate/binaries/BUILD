# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules/opentitan:cc.bzl", "exec_env_filegroup")

package(default_visibility = ["//visibility:public"])

exec_env_filegroup(
    name = "ate_gpio_toggle_test",
    testonly = True,
    exec_env = {
        "//hw/top_earlgrey:fpga_hyper310_rom_with_fake_keys": "cw310",
        "//hw/top_earlgrey:silicon_creator": "silicon",
    },
    files = {
        "ate_gpio_toggle_test_fpga_cw310_sival.signed.bin": "cw310",
        "ate_gpio_toggle_test_silicon_creator.signed.bin": "silicon",
    },
)
