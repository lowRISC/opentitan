# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load(
    "//rules:opentitan.bzl",
    "bin_to_vmem",
    "scramble_flash_vmem",
)

package(default_visibility = ["//visibility:public"])

filegroup(
    name = "presigned_fpga_cw310",
    srcs = ["empty_test_sigverify_spx_fpga_cw310.fake_rsa_prod_key_0.fake_spx_prod_key_0.signed.bin"],
)

filegroup(
    name = "presigned_fpga_cw310_bin",
    srcs = ["empty_test_sigverify_spx_fpga_cw310.fake_rsa_prod_key_0.fake_spx_prod_key_0.signed.bin"],
)

filegroup(
    name = "empty_test_fpga_cw310",
    srcs = ["empty_test_slot_a_fpga_cw310.signed.bin"],
)

filegroup(
    name = "empty_test_sim_dv",
    srcs = ["empty_test_slot_a_sim_dv.signed.bin"],
)

filegroup(
    name = "empty_test_sim_verilator",
    srcs = ["empty_test_slot_a_sim_verilator.signed.bin"],
)

filegroup(
    name = "rom_e2e_self_hash_fpga_cw310",
    srcs = ["rom_e2e_self_hash_fpga_cw310.signed.bin"],
)

filegroup(
    name = "rom_e2e_self_hash_sim_dv",
    srcs = ["rom_e2e_self_hash_sim_dv.signed.bin"],
)

bin_to_vmem(
    name = "rom_e2e_self_hash_sim_dv_vmem64",
    bin = ":rom_e2e_self_hash_sim_dv",
    word_size = 64,
)

scramble_flash_vmem(
    name = "rom_e2e_self_hash_sim_dv_scr_vmem64",
    otp = "//hw/ip/otp_ctrl/data:img_test_unlocked0",
    vmem = ":rom_e2e_self_hash_sim_dv_vmem64",
)

alias(
    name = "empty_test_fpga_cw310_bin",
    actual = "empty_test_fpga_cw310",
)

alias(
    name = "empty_test_sim_dv_bin",
    actual = "empty_test_sim_dv",
)

alias(
    name = "empty_test_sim_verilator_bin",
    actual = "empty_test_sim_verilator",
)

alias(
    name = "rom_e2e_self_hash_fpga_cw310_bin",
    actual = "rom_e2e_self_hash_fpga_cw310",
)

alias(
    name = "rom_e2e_self_hash_sim_dv_bin",
    actual = "rom_e2e_self_hash_sim_dv",
)
