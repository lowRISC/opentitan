# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:templates.bzl", "mako_template")
load("//hw/top:defs.bzl", "ALL_IP_NAMES", "opentitan_require_ip")
load("@ot_python_deps//:requirements.bzl", "requirement")

package(default_visibility = ["//visibility:public"])

[
    mako_template(
        name = "{}_{}".format(ip, suffix),
        data = [
            "//hw/top:top_desc",
        ],
        filename = filename,
        target_compatible_with = opentitan_require_ip(ip),
        template = template,
        variables = {
            "topcfg": "$(topinfo //hw/top:top_desc ip_map.{}.hjson)".format(ip),
            "ipcfg": "$(location $(topinfo //hw/top:top_desc ip_map.{}.hjson))".format(ip),
        },
        deps = [
            "//util/make_new_dif",
        ],
    )
    for ip in ALL_IP_NAMES
    for (suffix, template, filename) in [
        (
            "src",
            "dif_autogen.c.tpl",
            "dif_{}_autogen.c".format(ip),
        ),
        (
            "hdr",
            "dif_autogen.h.tpl",
            "dif_{}_autogen.h".format(ip),
        ),
        (
            "unittest",
            "dif_autogen_unittest.cc.tpl",
            "dif_{}_unittest.cc".format(ip),
        ),
    ]
]

[
    cc_library(
        name = ip,
        srcs = [":{}_src".format(ip)],
        hdrs = [":{}_hdr".format(ip)],
        deps = [
            "//hw/top:dt_{}".format(ip),
            "//hw/top:{}_c_regs".format(ip),
            "//sw/device/lib/base:mmio",
            "//sw/device/lib/dif:base",
        ],
    )
    for ip in ALL_IP_NAMES
]
