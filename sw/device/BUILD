# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:linker.bzl", "ld_library")

package(default_visibility = ["//visibility:public"])

ld_library(
    name = "info_sections",
    includes = ["info_sections.ld"],
)

config_setting(
    name = "measure_coverage_on_target",
    define_values = {
        "measure_coverage_on_target": "true",
    },
)

cc_library(
    name = "nothing",
)
