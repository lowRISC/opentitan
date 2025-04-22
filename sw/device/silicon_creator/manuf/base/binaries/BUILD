# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load(
    "//rules:opentitan.bzl",
    "bin_to_vmem",
    "scramble_flash_vmem",
)
load("//rules/opentitan:cc.bzl", "exec_env_filegroup")
load("//rules:files.bzl", "copy_files")

package(default_visibility = ["//visibility:public"])

copy_files(
    name = "copy_signed",
    testonly = True,
    srcs = [
        "//sw/device/silicon_creator/manuf/base:signed",
    ],
    filter = [
        "ft_personalize_sival",
    ],
    relative_to = ":BUILD",
    tags = ["manual"],
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

# The below rule sets (bin_to_vmem, scramble_flash_vmem, and filegroup)
# are needed to run the perso bin in sim.
bin_to_vmem(
    name = "ft_personalize_sival_silicon_creator_vmem64_signed",
    testonly = True,
    bin = ":ft_personalize_sival_silicon_creator.signed.bin",
    word_size = 64,  # Backdoor-load VMEM image uses 64-bit words
)

scramble_flash_vmem(
    name = "ft_personalize_sival_silicon_creator_scr_vmem64_signed",
    testonly = True,
    vmem = ":ft_personalize_sival_silicon_creator_vmem64_signed",
)

filegroup(
    name = "ft_personalize_sival_dv_files",
    testonly = True,
    srcs = [
        ":ft_personalize_sival_silicon_creator{}".format(file_type)
        for file_type in [
            ".signed.bin",
            "_vmem64_signed",
            "_scr_vmem64_signed",
        ]
    ],
)

# This alias is required for the DV testbench to locate these files.
filegroup(
    name = "ft_personalize_sival_silicon_creator",
    testonly = True,
    srcs = [":ft_personalize_sival_silicon_creator_vmem64_signed"],
)
