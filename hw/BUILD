# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

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
    visibility = [":__subpackages__"],
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
    visibility = [":__subpackages__"],
)

# This is used in CI steps that do not want to run Verilator tests, and thus
# do not want to build the Verilated model. This causes the //hw/top_{chip}:verilator
# target to not emit any files, which will break any tests that rely on this;
# builds will succeed, tests will fail.
config_setting(
    name = "disable_verilator_build",
    values = {"define": "DISABLE_VERILATOR_BUILD=true"},
    visibility = [":__subpackages__"],
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
    visibility = [":__subpackages__"],
)

# TODO(lowRISC/opentitan#7972): Globbing all of the //hw/... hierarchy together
# is a bit of a hack.  Longer term, we need proper rules for expressing the
# relationships between verilog components.
filegroup(
    name = "all_files",
    srcs = [
        "//hw/cdc:all_files",
        "//hw/data:all_files",
        "//hw/dv:all_files",
        "//hw/formal:all_files",
        "//hw/ip:all_files",
        "//hw/ip_templates:all_files",
        "//hw/lint:all_files",
        "//hw/rdc:all_files",
        "//hw/syn:all_files",
        "//hw/vendor:all_files",
        "//util:check_tool_requirements.py",
        "//util:tool_requirements.py",
    ],
    visibility = [":__subpackages__"],
)
