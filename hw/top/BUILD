# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@bazel_skylib//rules:common_settings.bzl", "string_flag")
load("//rules/opentitan:hw.bzl", "describe_top", "select_top_ld", "select_top_lib")
load("//rules/opentitan:util.bzl", "flatten")
load(
    "//rules:autogen.bzl",
    "opentitan_ip_c_header",
    "opentitan_ip_dt_header",
    "opentitan_ip_rust_header",
    "opentitan_top_dt_api",
)
load("//hw/top:defs.bzl", "ALL_IP_NAMES", "ALL_TOPS", "ALL_TOP_NAMES", "opentitan_if_ip", "opentitan_require_ip")

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

# C register headers for all IPs.
[
    opentitan_ip_c_header(
        name = "{}_c_regs".format(ip),
        ip = ip,
        target_compatible_with = opentitan_require_ip(ip),
        top = ":top_desc",
    )
    for ip in ALL_IP_NAMES
]

# Rust register headers for all IPs.
[
    opentitan_ip_rust_header(
        name = "{}_rust_regs".format(ip),
        ip = ip,
        target_compatible_with = opentitan_require_ip(ip),
        top = ":top_desc",
    )
    for ip in ALL_IP_NAMES
]

opentitan_top_dt_api(
    name = "dt_api",
    top = ":top_desc",
    deps = [":top_lib"],
)

[
    opentitan_ip_dt_header(
        name = "dt_{}".format(ip),
        ip = ip,
        target_compatible_with = opentitan_require_ip(ip),
        top = ":top_desc",
        deps = [":dt_api"],
    )
    for ip in ALL_IP_NAMES
]

cc_library(
    name = "dt_headers",
    hdrs = flatten([
        opentitan_if_ip(
            ip,
            ["dt_{}_hdr".format(ip)],
            [],
        )
        for ip in ALL_IP_NAMES
    ]),
    # Make the header accessible as "dt_<ip>.h".
    includes = ["."],
    deps = [":dt_api"],
)

[
    cc_library(
        name = "dt_{}".format(ip),
        srcs = [":dt_{}_src".format(ip)],
        deps = [":dt_headers"],
    )
    for ip in ALL_IP_NAMES
]

cc_library(
    name = "dt",
    srcs = [],
    deps = flatten([
        opentitan_if_ip(
            ip,
            ["dt_{}".format(ip)],
            [],
        )
        for ip in ALL_IP_NAMES
    ]),
)

cc_library(
    name = "doxy_target",
    deps = [
        # Pull all DT headers and implementation, transitively includes top headers.
        ":dt",
    ] + flatten([
        # Add all compatible register headers
        opentitan_if_ip(
            ip,
            ["{}_c_regs".format(ip)],
            [],
        )
        for ip in ALL_IP_NAMES
    ]),
)
