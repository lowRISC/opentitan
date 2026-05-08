# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules/opentitan:util.bzl", "flatten")
load(
    "//rules:autogen.bzl",
    "opentitan_ip_dt",
    "opentitan_top_dt_api",
)
load(
    "//hw/top:defs.bzl",
    "ALL_IP_NAMES",
    "opentitan_if_ip",
    "opentitan_require_ip",
    "opentitan_select_ip_attr",
)

package(default_visibility = ["//visibility:public"])

# DT binding extensions.

py_library(
    name = "clkmgr_ipconfig",
    srcs = ["clkmgr_ipconfig.py"],
    deps = [
        "//util/ipgen",
    ],
)

py_library(
    name = "clkmgr_binding",
    srcs = ["clkmgr_binding.py"],
    deps = [
        ":clkmgr_ipconfig",
        "//util/dtgen:helper",
        "//util/topgen",
    ],
)

py_library(
    name = "rstmgr_ipconfig",
    srcs = ["rstmgr_ipconfig.py"],
    deps = [
        "//util/ipgen",
    ],
)

py_library(
    name = "rstmgr_binding",
    srcs = ["rstmgr_binding.py"],
    deps = [
        ":rstmgr_ipconfig",
        "//util/dtgen:helper",
        "//util/topgen",
    ],
)

py_library(
    name = "pwrmgr_ipconfig",
    srcs = ["rstmgr_ipconfig.py"],
    deps = [
        "//util/ipgen",
    ],
)

py_library(
    name = "pwrmgr_binding",
    srcs = ["pwrmgr_binding.py"],
    deps = [
        ":pwrmgr_ipconfig",
        "//util/dtgen:helper",
        "//util/topgen",
    ],
)

# DT.

opentitan_top_dt_api(
    name = "api",
    deps = ["//hw/top:top_lib"],
)

[
    opentitan_ip_dt(
        name = "{}".format(ip),
        ip = ip,
        target_compatible_with = opentitan_require_ip(ip),
    )
    for ip in ALL_IP_NAMES
]

cc_library(
    name = "headers",
    hdrs = flatten([
        opentitan_if_ip(
            ip,
            ["{}_hdr".format(ip)],
            [],
        )
        for ip in ALL_IP_NAMES
    ]),
    deps = [":api"] + flatten([
        opentitan_select_ip_attr(
            ip,
            "dt_hdr_deps",
            default = [],
            required = False,
        )
        for ip in ALL_IP_NAMES
    ]),
)

[
    cc_library(
        name = "{}".format(ip),
        srcs = [":{}_src".format(ip)],
        deps = [":headers"] + opentitan_select_ip_attr(
            ip,
            "dt_src_deps",
            default = [],
            required = False,
        ),
    )
    for ip in ALL_IP_NAMES
]

cc_library(
    name = "dt",
    srcs = [],
    deps = flatten([
        opentitan_if_ip(
            ip,
            ["{}".format(ip)],
            [],
        )
        for ip in ALL_IP_NAMES
    ]),
)
