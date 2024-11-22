# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules/opentitan:cc.bzl", "exec_env_filegroup")

package(default_visibility = ["//visibility:public"])

exec_env_filegroup(
    name = "rom_ext_dice_x509_prod",
    testonly = True,
    exec_env = {
        "//hw/top_earlgrey:fpga_hyper310_rom_with_fake_keys": "cw310",
        "//hw/top_earlgrey:fpga_cw340_rom_with_fake_keys": "cw340",
        "//hw/top_earlgrey:silicon_creator": "silicon",
    },
    files = {
        "rom_ext_dice_x509_prod_slot_virtual_fpga_cw310.signed.bin": "cw310",
        "rom_ext_dice_x509_prod_slot_virtual_fpga_cw340.signed.bin": "cw340",
        "rom_ext_dice_x509_prod_slot_virtual_silicon_creator.signed.bin": "silicon",
    },
)

exec_env_filegroup(
    name = "rom_ext_dice_cwt_prod",
    testonly = True,
    exec_env = {
        "//hw/top_earlgrey:fpga_hyper310_rom_with_fake_keys": "cw310",
        "//hw/top_earlgrey:fpga_cw340_rom_with_fake_keys": "cw340",
        "//hw/top_earlgrey:silicon_creator": "silicon",
    },
    files = {
        "rom_ext_dice_cwt_prod_slot_virtual_fpga_cw310.signed.bin": "cw310",
        "rom_ext_dice_cwt_prod_slot_virtual_fpga_cw340.signed.bin": "cw340",
        "rom_ext_dice_cwt_prod_slot_virtual_silicon_creator.signed.bin": "silicon",
    },
)
