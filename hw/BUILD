# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_pkg//pkg:mappings.bzl", "pkg_files")
load("//rules:fusesoc.bzl", "fusesoc_build")

# This configuration exposes fusesoc's "verilator_options" option to the
# command line. This is intended to allow CI to specifically build a single
# -threaded Verilated model to suit it's resource constraints.
# By default, the Verilated model should be built to
# run with 4 threads.
load("@bazel_skylib//rules:common_settings.bzl", "string_list_flag")

string_list_flag(
    name = "verilator_options",
    build_setting_default = [
        "--threads",
        "4",
    ],
)

# This configuration exposes fusesoc's "make_options" to enable parallel
# compilation of the verilated model. Compilation takes about 30m of cpu time
# and 5m of time that isn't parallelized by this option, so this should reduce
# the total runtime to ~12m.
string_list_flag(
    name = "make_options",
    build_setting_default = [
        "-j",
        "4",
    ],
)

fusesoc_build(
    name = "verilator_real",
    srcs = [
        ":all_files",
    ],
    cores = [
        "//:cores",
    ],
    data = ["//hw/ip/otbn:all_files"],
    make_options = ":make_options",
    output_groups = {
        "binary": ["sim-verilator/Vchip_sim_tb"],
    },
    systems = ["lowrisc:dv:chip_verilator_sim"],
    tags = [
        "manual",
        "verilator",
    ],
    target = "sim",
    verilator_options = ":verilator_options",
)

filegroup(
    name = "verilator_bin",
    srcs = [":verilator_real"],
    output_group = "binary",
)

# This is used in CI steps that do not want to run Verilator tests, and thus
# do not want to build the Verilated model. This causes the //hw:verilator
# target to not emit any files, which will break any tests that rely on this;
# builds will succeed, tests will fail.
config_setting(
    name = "disable_verilator_build",
    values = {"define": "DISABLE_VERILATOR_BUILD=true"},
)

genrule(
    name = "verilator_stub",
    outs = ["Vfake_sim_tb"],
    cmd = """
        script=$@
        echo '#!/bin/bash' > $$script
        echo 'echo "ERROR: sim_verilator tests cannot be run when --define DISABLE_VERILATOR_BUILD=true is set!"' >> $$script
        echo 'echo "This indicates an error in your Bazel invokation"' >> $$script
        echo 'exit 1' >> $$script
        chmod +x $@
    """,
)

alias(
    name = "verilator",
    actual = select({
        ":disable_verilator_build": ":verilator_stub",
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

# TODO(lowRISC/opentitan#7972): Globbing all of the //hw/... hierarchy together
# is a bit of a hack.  Longer term, we need proper rules for expressing the
# relationships between verilog components.
filegroup(
    name = "all_files",
    srcs = glob(
        ["**"],
        # TODO(lowRISC/opentitan#15882): make Verilator work with foundry repo present.
        exclude = ["foundry/**"],
    ) + [
        "//:tool_requirements.py",
        "//hw/ip:all_files",
        "//hw/top_earlgrey:all_files",
        "//util:check_tool_requirements.py",
    ],
    visibility = ["//visibility:public"],
)

pkg_files(
    name = "package",
    srcs = ["verilator_bin"],
    prefix = "earlgrey/verilator",
    visibility = ["//visibility:public"],
)
