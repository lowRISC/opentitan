# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:linker.bzl", "ld_library")

package(default_visibility = ["//visibility:public"])

ld_library(
    name = "info_sections",
    includes = ["info_sections.ld"],
    deps = [
        "//sw/device/lib/coverage:coverage_sections",
    ],
)

# FIXME(lowRISC/opentitan#12065) This is a hack to work around currently
# only supporting one top.
#
# See //hw/top_englishbreakfast/util/prepare_sw.py for where this is set.
config_setting(
    name = "is_english_breakfast",
    values = {"copt": "-DOT_IS_ENGLISH_BREAKFAST_REDUCED_SUPPORT_FOR_INTERNAL_USE_ONLY_"},
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
