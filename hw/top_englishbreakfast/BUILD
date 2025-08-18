# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@bazel_skylib//rules:common_settings.bzl", "string_list_flag")
load("//rules:fusesoc.bzl", "fusesoc_build")
load(
    "//rules/opentitan:defs.bzl",
    "DEFAULT_TEST_FAILURE_MSG",
    "DEFAULT_TEST_SUCCESS_MSG",
    "sim_verilator",
)

package(default_visibility = ["//visibility:public"])

filegroup(
    name = "rtl_files",
    srcs = glob(
        ["**"],
    ) + [
        "//hw/top_englishbreakfast/ip:rtl_files",
    ],
)

fusesoc_build(
    name = "verilator_sim",
    srcs = [
        ":rtl_files",
        "//hw:dpi_files",
        "//hw:dv_common_files",
        "//hw:rtl_files",
        "//hw:verilator_files",
    ],
    cores = [
        "//hw:cores",
    ],
    data = ["//hw/ip/otbn:rtl_files"],
    make_options = ":make_options",
    output_groups = {
        "binary": ["lowrisc_systems_chip_englishbreakfast_verilator_0.1/sim-verilator/Vchip_englishbreakfast_verilator"],
    },
    systems = ["lowrisc:systems:chip_englishbreakfast_verilator"],
    tags = [
        "manual",
        "verilator",
    ],
    target = "sim",
    verilator_options = ":verilator_options",
)

string_list_flag(
    name = "verilator_options",
    build_setting_default = [
        "--threads",
        "2",
    ],
)

string_list_flag(
    name = "make_options",
    build_setting_default = [
        "-j",
        "2",
    ],
)

###########################################################################
# Sim Verilator Environments
#
# The sim_verilator_base target is only meant to be used for building ROMs
# and other items without `testonly=True`.
###########################################################################
sim_verilator(
    name = "sim_verilator_base",
    design = "englishbreakfast",
    exec_env = "sim_verilator",
    libs = [
        "//sw/device/lib/arch:boot_stage_rom_ext",
        "//sw/device/lib/arch:sim_verilator",
        "//hw/top_englishbreakfast/sw/dt:sim_verilator",
    ],
    linker_script = "//sw/device/lib/testing/test_framework:ottf_ld_silicon_creator_slot_a",
    test_cmd = "testing-not-supported",
)

sim_verilator(
    name = "sim_verilator",
    testonly = True,
    args = [
        "--rcfile=",
        "--logging=debug",
        "--interface=verilator",
        "--verilator-bin=$(rootpath //hw/top_englishbreakfast:verilator_sim)",
        "--verilator-rom={rom}",
        "--verilator-flash={firmware}",
    ],
    base = ":sim_verilator_base",
    data = [
        ":verilator_sim",
    ],
    exec_env = "sim_verilator",
    param = {
        "exit_success": DEFAULT_TEST_SUCCESS_MSG,
        "exit_failure": DEFAULT_TEST_FAILURE_MSG,
    },
    rom = "//sw/device/lib/testing/test_rom:test_rom",
    test_cmd = """
        --exec="console --non-interactive --exit-success='{exit_success}' --exit-failure='{exit_failure}'"
        no-op
    """,
)
