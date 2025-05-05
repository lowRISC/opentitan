# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules/opentitan:cc.bzl", "exec_env_filegroup")
load("//rules/opentitan:legacy.bzl", "scramble_flash_vmem", "vmem_file")

package(default_visibility = ["//visibility:public"])

exec_env_filegroup(
    name = "ate_gpio_toggle_test_bins",
    testonly = True,
    exec_env = {
        "//hw/top_earlgrey:fpga_hyper310_rom_with_fake_keys": "cw310",
        "//hw/top_earlgrey:silicon_creator": "silicon",
        "//hw/top_earlgrey:sim_dv": "sim_dv",
    },
    files = {
        "ate_gpio_toggle_test_fpga_cw310_sival.signed.bin": "cw310",
        "ate_gpio_toggle_test_silicon_creator.signed.bin": "silicon",
        "ate_gpio_toggle_test_sim_dv.signed.bin": "sim_dv",
    },
)

# The below rule sets (bin_to_vmem, scramble_flash_vmem, and filegroup)
# are needed to run the ATE GPIO toggle test in DV.
_DV_EXEC_ENVS = [
    "sim_dv",
    "silicon_creator",
]

[
    vmem_file(
        name = "ate_gpio_toggle_test_{}_vmem64_signed".format(env),
        testonly = True,
        src = ":ate_gpio_toggle_test_{}.signed.bin".format(env),
        word_size = 64,  # Backdoor-load VMEM image uses 64-bit words
    )
    for env in _DV_EXEC_ENVS
]

[
    scramble_flash_vmem(
        name = "ate_gpio_toggle_test_{}_scr_vmem64_signed".format(env),
        testonly = True,
        src = ":ate_gpio_toggle_test_{}_vmem64_signed".format(env),
    )
    for env in _DV_EXEC_ENVS
]

filegroup(
    name = "ate_gpio_toggle_test_dv_files",
    testonly = True,
    srcs = [
        ":ate_gpio_toggle_test_{}{}".format(env, file_type)
        for env in _DV_EXEC_ENVS
        for file_type in [
            ".signed.bin",
            "_vmem64_signed",
            "_scr_vmem64_signed",
        ]
    ],
)

# This alias is required for the DV testbench to locate these files.
filegroup(
    name = "ate_gpio_toggle_test_silicon_creator",
    testonly = True,
    srcs = [
        ":ate_gpio_toggle_test_silicon_creator.dis",
        ":ate_gpio_toggle_test_silicon_creator_vmem64_signed",
    ],
)
