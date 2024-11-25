# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@bazel_skylib//rules:common_settings.bzl", "string_flag")
load(
    "//rules:autogen.bzl",
    "opentitan_ip_c_header",
    "opentitan_ip_dt_header",
    "opentitan_ip_rust_header",
    "opentitan_top_devicetables",
    "opentitan_top_dt_api",
)
load("//hw/top:defs.bzl", IPS = "OPENTITAN_ALL_IPS")

package(default_visibility = ["//visibility:public"])

ALL_TOPS = [
    "earlgrey",
    "darjeeling",
]

# Use this flag to select the top.
string_flag(
    name = "top",
    build_setting_default = "earlgrey",
    values = ALL_TOPS,
)

# Config settings to test against tops.
[
    config_setting(
        name = "is_{}".format(top),
        flag_values = {
            ":top": top,
        },
    )
    for top in ALL_TOPS
]

alias(
    name = "top_desc",
    actual = select(
        {
            ":is_earlgrey": "//hw/top_earlgrey",
            ":is_darjeeling": "//hw/top_darjeeling",
        },
        no_match_error = "unknown top",
    ),
)

alias(
    name = "top_lib",
    actual = select(
        {
            ":is_earlgrey": "//hw/top_earlgrey/sw/autogen:top_earlgrey",
            ":is_darjeeling": "//hw/top_darjeeling/sw/autogen:top_darjeeling",
        },
        no_match_error = "unknown top",
    ),
)

[
    opentitan_ip_c_header(
        name = "{}_c_regs".format(ip),
        ip = ip,
        top = ":top_desc",
    )
    for ip in IPS
]

[
    opentitan_ip_rust_header(
        name = "{}_rust_regs".format(ip),
        ip = ip,
        top = ":top_desc",
    )
    for ip in IPS
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
        top = ":top_desc",
        deps = [":dt_api"],
    )
    for ip in IPS
]

cc_library(
    name = "dt_headers",
    srcs = [],
    deps = ["dt_{}".format(ip) for ip in IPS],
)

opentitan_top_devicetables(
    name = "devicetables",
    top = ":top_desc",
    deps = [":dt_headers"],
)
