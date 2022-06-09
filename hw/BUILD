# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:fusesoc.bzl", "fusesoc_build")

# This configuration exposes fusesoc's "verilator_options" option to the
# command line. This is intended to allow CI to specifically build a single
# -threaded Verilator model since the build environment there is more resource
# -constrained.
# By default and in all other cases, the Verilator model should be built to
# run with 4 threads.
load("@bazel_skylib//rules:common_settings.bzl", "string_list_flag")

string_list_flag(
    name = "verilator_options",
    build_setting_default = [
        "--threads",
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
    flags = ["--verilator_options=--threads 1"],
    systems = ["lowrisc:dv:chip_verilator_sim"],
    tags = ["verilator"],
    target = "sim",
    verilator_options = ":verilator_options",
)

# This is used in CI steps that do not want to run Verilator tests, and thus
# do not want to accidentally build the Verilator model. This causes the
# //hw:verilator target to not emit any files, which will break any tests that
# actually rely on this; builds will succeed, tests will fail.
#
# FIXME(lowRISC/opentitan#12259): This is a temporary workaround.
config_setting(
    name = "disable_verilator_build",
    values = {"define": "DISABLE_VERILATOR_BUILD=true"},
)

genrule(
    name = "verilator_stub",
    outs = ["verilator-stub"],
    cmd = """
        mkdir -p $@/sim-verilator
        script=$@/sim-verilator/Vchip_sim_tb
        echo '#!/bin/bash' > $$script
        echo 'echo "ERROR: sim_verilator tests cannot be run when --define DISABLE_VERILATOR_BUILD=true is set!"' >> $$script
        echo 'echo "This indicates an error in your Bazel invokation"' >> $$script
        echo 'exit 1' >> $$script
        chmod +x $@/sim-verilator/Vchip_sim_tb
    """,
)

alias(
    name = "verilator",
    actual = select({
        ":disable_verilator_build": ":verilator-stub",
        "//conditions:default": ":verilator_real",
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
        exclude = ["dv/tools/ralgen/*"],
    ) + [
        "//hw/ip:all_files",
        "//hw/top_earlgrey:all_files",
    ],
    visibility = ["//visibility:public"],
)
