# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules/opentitan:cc.bzl", "exec_env_filegroup")

package(default_visibility = ["//visibility:public"])

filegroup(
    name = "perso_bins",
    srcs = [
        "ft_personalize_sival_fpga_cw340_rom_with_fake_keys.signed.bin",
        "ft_personalize_sival_fpga_hyper310_rom_with_fake_keys.signed.bin",
        "ft_personalize_sival_silicon_creator.signed.bin",
    ],
)

exec_env_filegroup(
    name = "ft_personalize_sival",
    testonly = True,
    exec_env = {
        "//hw/top_earlgrey:fpga_hyper310_rom_with_fake_keys": "cw310",
        "//hw/top_earlgrey:fpga_cw340_rom_with_fake_keys": "cw340",
        "//hw/top_earlgrey:silicon_creator": "silicon",
    },
    files = {
        "ft_personalize_sival_fpga_hyper310_rom_with_fake_keys.signed.bin": "cw310",
        "ft_personalize_sival_fpga_cw340_rom_with_fake_keys.signed.bin": "cw340",
        "ft_personalize_sival_silicon_creator.signed.bin": "silicon",
    },
)
