# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@bazel_skylib//rules:common_settings.bzl", "string_list_flag")

package(default_visibility = ["//visibility:public"])

filegroup(
    name = "doc_files",
    srcs = glob(["**/*.md"]) + [
        "//sw/device:doc_files",
        "//sw/host:doc_files",
    ],
)

# A build flag for specifying preferred execution environments as a list of strings.
# Priority from highest to lowest.
string_list_flag(
    name = "exec_env",
    build_setting_default = [
        "fpga_cw340$",
        "fpga_cw340_test_rom$",
        "fpga_cw340_rom_with_fake_keys$",
        "fpga_cw340_rom_ext$",
        "fpga_cw340_sival$",
        "fpga_cw340_sival_rom_ext$",
        "fpga_cw310$",
        "fpga_cw310_test_rom$",
        "fpga_cw310_rom_with_fake_keys$",
        "fpga_cw310_rom_ext$",
        "fpga_cw310_sival$",
        "fpga_cw310_sival_rom_ext$",
        "sim_qemu_base$",
        "sim_qemu_rom_with_fake_keys$",
        "sim_verilator_base$",
        "sim_verilator$",
        "sim_verilator_rom_with_fake_keys$",
        "sim_dv_base$",
        "sim_dv$",
        "fpga_cw305$",
        "silicon_creator$",
        "silicon_owner_sival_rom_ext$",
        "",  # wildcard
    ],
)
