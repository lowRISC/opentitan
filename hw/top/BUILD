# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@bazel_skylib//rules:common_settings.bzl", "string_flag")
load("//rules/opentitan:hw.bzl", "select_top", "select_top_lib")
load(
    "//rules:autogen.bzl",
    "opentitan_ip_c_header",
    "opentitan_ip_rust_header",
)
load("//hw/top:defs.bzl", "ALL_IP_NAMES", "ALL_TOPS", "ALL_TOP_NAMES", "opentitan_require_ip")

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
    select_top(
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
    opentitan_ip_c_header(
        name = "{}_c_regs".format(ip),
        ip = ip,
        target_compatible_with = opentitan_require_ip(ip),
        top = ":top_desc",
    )
    for ip in ALL_IP_NAMES
]

[
    opentitan_ip_rust_header(
        name = "{}_rust_regs".format(ip),
        ip = ip,
        target_compatible_with = opentitan_require_ip(ip),
        top = ":top_desc",
    )
    for ip in ALL_IP_NAMES
]
