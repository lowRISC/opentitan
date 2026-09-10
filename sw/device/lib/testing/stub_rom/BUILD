# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules/opentitan:defs.bzl", "opentitan_binary")
load("//rules:linker.bzl", "ld_library")
load("//rules/opentitan:legacy.bzl", "legacy_rom_targets")
load(
    "//rules/opentitan:defs.bzl",
    "OPENTITAN_CPU",
    "opentitan_binary",
)

package(default_visibility = ["//visibility:public"])

ld_library(
    name = "linker_script",
    script = "stub_rom.ld",
    deps = [
        "//hw/top:top_ld",
    ],
)

cc_library(
    name = "stub_rom_lib",
    srcs = ["stub_rom.S"],
    target_compatible_with = [OPENTITAN_CPU],
)

opentitan_binary(
    name = "stub_rom",
    collect_code_coverage = 0,
    exec_env = [
        "//hw/top_earlgrey:fpga_cw305",
        "//hw/top_earlgrey:fpga_cw340",
    ],
    features = ["use_lld"],
    kind = "rom",
    linker_script = ":linker_script",
    deps = [
        ":stub_rom_lib",
    ],
)

legacy_rom_targets(
    suffixes = {
        "fpga_cw305": ["//hw/top_earlgrey:fpga_cw305"],
        "fpga_cw340": ["//hw/top_earlgrey:fpga_cw340"],
    },
    target = "stub_rom",
)
