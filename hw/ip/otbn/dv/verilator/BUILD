# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:fusesoc.bzl", "fusesoc_build")

package(default_visibility = ["//visibility:public"])

load("@bazel_skylib//rules:common_settings.bzl", "string_list_flag")

string_list_flag(
    name = "verilator_options",
    build_setting_default = [
        "--threads",
        "1",
    ],
)

fusesoc_build(
    name = "otbn_sim_verilator",
    srcs = [
        ":otbn_mock_edn.sv",
        ":otbn_top_sim.cc",
        ":otbn_top_sim.sv",
        ":otbn_top_sim_waivers.vlt",
        "//hw:all_files",
    ],
    cores = [
        ":otbn_top_sim.core",
        "//:cores",
    ],
    data = [
        "//hw/ip/otbn:all_files",
    ],
    output_groups = {
        "binary": ["sim-verilator/Votbn_top_sim"],
    },
    systems = ["lowrisc:ip:otbn_top_sim"],
    tags = [
        "manual",
        "verilator",
    ],
    target = "sim",
    verilator_options = ":verilator_options",
)
