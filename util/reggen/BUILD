# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_python//python:defs.bzl", "py_library")
load("@ot_python_deps//:requirements.bzl", "requirement")

package(default_visibility = ["//visibility:public"])

py_library(
    name = "lib",
    srcs = ["lib.py"],
)

py_library(
    name = "access",
    srcs = ["access.py"],
    deps = [":lib"],
)

py_library(
    name = "alert",
    srcs = ["alert.py"],
    deps = [
        ":bits",
        ":lib",
        ":signal",
    ],
)

py_library(
    name = "bits",
    srcs = ["bits.py"],
    deps = [
        ":lib",
        ":params",
    ],
)

py_library(
    name = "bus_interfaces",
    srcs = ["bus_interfaces.py"],
    deps = [
        ":inter_signal",
        ":lib",
    ],
)

py_library(
    name = "clocking",
    srcs = ["clocking.py"],
    deps = [":lib"],
)

py_library(
    name = "countermeasure",
    srcs = ["countermeasure.py"],
    deps = [":lib"],
)

py_library(
    name = "enum_entry",
    srcs = ["enum_entry.py"],
    deps = [":lib"],
)

py_library(
    name = "field",
    srcs = ["field.py"],
    deps = [
        ":access",
        ":bits",
        ":enum_entry",
        ":lib",
        ":params",
        "//util/design/mubi:prim_mubi",
    ],
)

py_library(
    name = "interrupt",
    srcs = ["interrupt.py"],
    deps = [
        ":bits",
        ":lib",
        ":signal",
    ],
)

py_library(
    name = "html_helpers",
    srcs = ["html_helpers.py"],
)

py_library(
    name = "inter_signal",
    srcs = ["inter_signal.py"],
    deps = [":lib"],
)

py_library(
    name = "ip_block",
    srcs = ["ip_block.py"],
    deps = [
        ":alert",
        ":bus_interfaces",
        ":clocking",
        ":countermeasure",
        ":inter_signal",
        ":interrupt",
        ":lib",
        ":params",
        ":reg_block",
        ":signal",
        requirement("hjson"),
    ],
)

py_library(
    name = "params",
    srcs = ["params.py"],
    deps = [":lib"],
)

py_library(
    name = "reg_base",
    srcs = ["reg_base.py"],
    deps = [":field"],
)

py_library(
    name = "reg_block",
    srcs = ["reg_block.py"],
    deps = [
        ":access",
        ":alert",
        ":bus_interfaces",
        ":clocking",
        ":field",
        ":lib",
        ":multi_register",
        ":params",
        ":register",
        ":signal",
        ":window",
    ],
)

py_library(
    name = "register",
    srcs = ["register.py"],
    deps = [
        ":access",
        ":clocking",
        ":field",
        ":lib",
        ":params",
        ":reg_base",
    ],
)

py_library(
    name = "multi_register",
    srcs = ["multi_register.py"],
    deps = [
        ":clocking",
        ":field",
        ":lib",
        ":params",
        ":reg_base",
        ":register",
    ],
)

py_library(
    name = "signal",
    srcs = ["signal.py"],
    deps = [
        ":bits",
        ":lib",
    ],
)

py_library(
    name = "window",
    srcs = ["window.py"],
    deps = [
        ":access",
        ":lib",
        ":params",
    ],
)

py_library(
    name = "gen_cheader",
    srcs = ["gen_cheader.py"],
    deps = [
        ":field",
        ":ip_block",
        ":multi_register",
        ":params",
        ":register",
        ":signal",
        ":window",
    ],
)

py_library(
    name = "gen_dv",
    srcs = ["gen_dv.py"],
    deps = [
        ":ip_block",
        ":multi_register",
        ":register",
        ":window",
        requirement("mako"),
        requirement("pyyaml"),
    ],
)

py_library(
    name = "gen_fpv",
    srcs = ["gen_fpv.py"],
    deps = [
        ":ip_block",
        requirement("mako"),
        requirement("pyyaml"),
    ],
)

py_library(
    name = "gen_html",
    srcs = ["gen_html.py"],
    deps = [
        ":html_helpers",
        ":ip_block",
        ":multi_register",
        ":reg_block",
        ":register",
        ":window",
        requirement("mistletoe"),
    ],
)

py_library(
    name = "gen_json",
    srcs = ["gen_json.py"],
    deps = [requirement("hjson")],
)

py_library(
    name = "gen_rtl",
    srcs = ["gen_rtl.py"],
    deps = [
        ":ip_block",
        ":lib",
        ":multi_register",
        ":reg_base",
        ":register",
        requirement("mako"),
    ],
)

py_library(
    name = "gen_rust",
    srcs = ["gen_rust.py"],
    deps = [
        ":field",
        ":ip_block",
        ":multi_register",
        ":params",
        ":register",
        ":signal",
        ":window",
    ],
)

py_library(
    name = "gen_tock",
    srcs = ["gen_tock.py"],
    deps = [
        ":field",
        ":ip_block",
        ":multi_register",
        ":params",
        ":register",
        ":signal",
        ":window",
    ],
)

py_library(
    name = "gen_sec_cm_testplan",
    srcs = ["gen_sec_cm_testplan.py"],
    deps = [
        ":ip_block",
        requirement("hjson"),
        requirement("mako"),
    ],
)

py_library(
    name = "gen_selfdoc",
    srcs = ["gen_selfdoc.py"],
    deps = [
        ":access",
        ":enum_entry",
        ":field",
        ":ip_block",
        ":multi_register",
        ":register",
        ":validate",
        ":window",
    ],
)

py_library(
    name = "validate",
    srcs = ["validate.py"],
)

py_library(
    name = "version",
    srcs = ["version.py"],
)

filegroup(
    name = "tpl_files",
    srcs = glob(["**/*.tpl"]),
)
