# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

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

# FIXME rework that properly with platforms
constraint_setting(
    name = "top_setting",
    default_constraint_value = ":top_earlgrey",
)

constraint_value(
    name = "top_earlgrey",
    constraint_setting = ":top_setting",
)

alias(
    name = "top",
    actual = select(
        {
            ":top_earlgrey": "//hw/top_earlgrey",
        },
        no_match_error = "no top selected",
    ),
)

alias(
    name = "top_lib",
    actual = select(
        {
            ":top_earlgrey": "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        },
        no_match_error = "no top selected",
    ),
)

[
    opentitan_ip_c_header(
        name = "{}_c_regs".format(ip),
        ip = ip,
        top = ":top",
    )
    for ip in IPS
]

[
    opentitan_ip_rust_header(
        name = "{}_rust_regs".format(ip),
        ip = ip,
        top = ":top",
    )
    for ip in IPS
]

opentitan_top_dt_api(
    name = "dt_api",
    top = ":top",
    deps = [":top_lib"],
)

[
    opentitan_ip_dt_header(
        name = "dt_{}".format(ip),
        ip = ip,
        top = ":top",
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
    top = ":top",
    deps = [":dt_headers"],
)
