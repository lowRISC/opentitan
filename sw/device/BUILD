# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:linker.bzl", "ld_library")

package(default_visibility = ["//visibility:public"])

ld_library(
    name = "info_sections",
    includes = ["info_sections.ld"],
)

# FIXME(lowRISC/opentitan#12065) This is a hack to work around currently
# only supporting one top.
#
# See //hw/top_englishbreakfast/util/prepare_sw.py for where this is set.
config_setting(
    name = "is_english_breakfast",
    values = {"copt": "-DOT_IS_ENGLISH_BREAKFAST_REDUCED_SUPPORT_FOR_INTERNAL_USE_ONLY_"},
)

cc_library(
    name = "nothing",
)
