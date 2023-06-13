# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load(
    "//rules:opentitan.bzl",
    "bin_to_vmem",
    "scramble_flash_vmem",
)

package(default_visibility = ["//visibility:public"])

# Pre-signed empty test binaries and aliases.
_EMPTY_TEST_DEVICES = [
    "sim_dv",
    "sim_verilator",
    "fpga_cw310",
]

[
    filegroup(
        name = "empty_test_{}".format(dev),
        srcs = ["empty_test_sigverify_spx_{}.signed.bin".format(dev)],
    )
    for dev in _EMPTY_TEST_DEVICES
]

[
    alias(
        name = "empty_test_{}_bin".format(dev),
        actual = ":empty_test_{}".format(dev),
    )
    for dev in _EMPTY_TEST_DEVICES
]

# ROM self hash test binaries and aliases.
bin_to_vmem(
    name = "rom_e2e_self_hash_sim_dv_vmem64",
    bin = "rom_e2e_self_hash_sim_dv.signed.bin",
    word_size = 64,
)

scramble_flash_vmem(
    name = "rom_e2e_self_hash_sim_dv_scr_vmem64",
    otp = "//hw/ip/otp_ctrl/data:img_test_unlocked0",
    vmem = ":rom_e2e_self_hash_sim_dv_vmem64",
)

[
    filegroup(
        name = "rom_e2e_self_hash_{}".format(dev),
        srcs = [
            "rom_e2e_self_hash_{}.signed.bin".format(dev),
        ] + [] if dev == "fpga_cw310" else [
            ":rom_e2e_self_hash_{}_scr_vmem64".format(dev),
            ":rom_e2e_self_hash_{}_vmem64".format(dev),
        ],
    )
    for dev in [
        "sim_dv",
        "fpga_cw310",
    ]
]

alias(
    name = "rom_e2e_self_hash_fpga_cw310_bin",
    actual = ":rom_e2e_self_hash_fpga_cw310",
)
