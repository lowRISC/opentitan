# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

package(default_visibility = ["//visibility:public"])

load("@rules_pkg//pkg:mappings.bzl", "pkg_files")
load("//rules:fusesoc.bzl", "fusesoc_build")
load("//rules:autogen.bzl", "autogen_hjson_header")

autogen_hjson_header(
    name = "rv_plic_regs",
    srcs = [
        "ip_autogen/rv_plic/data/rv_plic.hjson",
    ],
)

autogen_hjson_header(
    name = "alert_handler_regs",
    srcs = [
        "ip_autogen/alert_handler/data/alert_handler.hjson",
    ],
)

filegroup(
    name = "all_files",
    srcs = glob(["**"]) + [
        "//hw:all_files",
        "//hw/top_darjeeling/data:all_files",
        "//hw/top_darjeeling/dv/verilator:all_files",
        "//hw/top_darjeeling/ip:all_files",
        "//hw/top_darjeeling/sw:all_files",
    ],
)

filegroup(
    name = "cores",
    srcs = glob(["**/*.core"]),
)

fusesoc_build(
    name = "verilator_real",
    srcs = [
        ":all_files",
    ],
    cores = [
        "//util:cores",
        "//hw/dv:cores",
        "//hw/formal:cores",
        "//hw/ip:cores",
        "//hw/ip_templates:cores",
        "//hw/lint:cores",
        "//hw/vendor:cores",
        "//hw/top_darjeeling:cores",
    ],
    data = ["//hw/ip/otbn:all_files"],
    make_options = "//hw:make_options",
    output_groups = {
        "binary": ["sim-verilator/Vchip_sim_tb"],
    },
    systems = ["lowrisc:dv:chip_darjeeling_verilator_sim"],
    tags = [
        "manual",
        "verilator",
    ],
    target = "sim",
    verilator_options = "//hw:verilator_options",
)

filegroup(
    name = "verilator_bin",
    srcs = [":verilator_real"],
    output_group = "binary",
)

alias(
    name = "verilator",
    actual = select({
        "//hw:disable_verilator_build": "//hw:verilator_stub",
        "//conditions:default": ":verilator_bin",
    }),
    tags = ["verilator"],
    visibility = ["//visibility:public"],
)

genrule(
    name = "fusesoc_ignore",
    outs = ["FUSESOC_IGNORE"],
    cmd = """
        touch $@
    """,
    visibility = ["//visibility:public"],
)

pkg_files(
    name = "package",
    srcs = ["verilator_bin"],
    prefix = "darjeeling/verilator",
    visibility = ["//visibility:public"],
)
