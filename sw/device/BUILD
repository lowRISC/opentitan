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
        "ot_coverage_enabled": "true",
    },
    deprecation = "Please use //rules/coverage:enabled instead.",
)

cc_library(
    name = "nothing",
)

filegroup(
    name = "doc_files",
    srcs = glob(["**/*.md"]) + [
        "//sw/device/lib:doc_files",
        "//sw/device/lib/base:doc_files",
        "//sw/device/lib/crypto/data:doc_files",
        "//sw/device/lib/dif:doc_files",
        "//sw/device/lib/testing:doc_files",
        "//sw/device/lib/testing/test_framework:doc_files",
        "//sw/device/silicon_creator:doc_files",
        "//sw/device/tests:doc_files",
    ],
)
