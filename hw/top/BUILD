# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@bazel_skylib//rules:common_settings.bzl", "string_flag")
load("//rules/opentitan:hw.bzl", "describe_top", "select_top_ld", "select_top_lib")
load("//hw/top:defs.bzl", "ALL_TOPS", "ALL_TOP_NAMES")

package(default_visibility = ["//visibility:public"])

# Use this flag to select the top.
string_flag(
    name = "top",
    build_setting_default = "earlgrey",
    values = ALL_TOP_NAMES,
)

# Config settings to test against tops.
[
    config_setting(
        name = "is_{}".format(top),
        flag_values = {
            ":top": top,
        },
    )
    for top in ALL_TOP_NAMES
]

[
    describe_top(
        name = "top_{}_desc".format(top),
        all_tops = ALL_TOPS,
        top = top,
    )
    for top in ALL_TOP_NAMES
]

# Point to the right top description.
alias(
    name = "top_desc",
    actual = select({
        "is_{}".format(top): ":top_{}_desc".format(top)
        for top in ALL_TOP_NAMES
    }),
)

[
    select_top_lib(
        name = "top_{}_lib".format(top),
        all_tops = ALL_TOPS,
        top = top,
    )
    for top in ALL_TOP_NAMES
]

# Point to the right top library.
alias(
    name = "top_lib",
    actual = select({
        "is_{}".format(top): ":top_{}_lib".format(top)
        for top in ALL_TOP_NAMES
    }),
)

[
    select_top_ld(
        name = "top_{}_ld".format(top),
        all_tops = ALL_TOPS,
        top = top,
    )
    for top in ALL_TOP_NAMES
]

# Point to the right top library.
alias(
    name = "top_ld",
    actual = select({
        "is_{}".format(top): ":top_{}_ld".format(top)
        for top in ALL_TOP_NAMES
    }),
)
