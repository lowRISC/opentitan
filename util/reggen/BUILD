# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_python//python:defs.bzl", "py_library")
load("@ot_python_deps//:requirements.bzl", "requirement")

package(default_visibility = ["//visibility:public"])

py_library(
    name = "lib",
    srcs = ["lib.py"],
    imports = [".."],
)

py_library(
    name = "access",
    srcs = ["access.py"],
    imports = [".."],
    deps = [":lib"],
)

py_library(
    name = "alert",
    srcs = ["alert.py"],
    imports = [".."],
    deps = [
        ":bits",
        ":lib",
        ":signal",
    ],
)

py_library(
    name = "bits",
    srcs = ["bits.py"],
    imports = [".."],
    deps = [
        ":lib",
        ":params",
    ],
)

py_library(
    name = "bus_interfaces",
    srcs = ["bus_interfaces.py"],
    imports = [".."],
    deps = [
        ":inter_signal",
        ":lib",
    ],
)

py_library(
    name = "clocking",
    srcs = ["clocking.py"],
    imports = [".."],
    deps = [":lib"],
)

py_library(
    name = "countermeasure",
    srcs = ["countermeasure.py"],
    imports = [".."],
    deps = [":lib"],
)

py_library(
    name = "enum_entry",
    srcs = ["enum_entry.py"],
    imports = [".."],
    deps = [":lib"],
)

py_library(
    name = "field",
    srcs = ["field.py"],
    imports = [".."],
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
    imports = [".."],
    deps = [
        ":bits",
        ":lib",
        ":signal",
    ],
)

py_library(
    name = "html_helpers",
    srcs = ["html_helpers.py"],
    imports = [".."],
)

py_library(
    name = "inter_signal",
    srcs = ["inter_signal.py"],
    imports = [".."],
    deps = [":lib"],
)

py_library(
    name = "ip_block",
    srcs = ["ip_block.py"],
    imports = [".."],
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
        requirement("semantic_version"),
    ],
)

py_library(
    name = "params",
    srcs = ["params.py"],
    imports = [".."],
    deps = [":lib"],
)

py_library(
    name = "reg_base",
    srcs = ["reg_base.py"],
    imports = [".."],
    deps = [":field"],
)

py_library(
    name = "reg_block",
    srcs = ["reg_block.py"],
    imports = [".."],
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
        requirement("semantic_version"),
    ],
)

py_library(
    name = "register",
    srcs = ["register.py"],
    imports = [".."],
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
    imports = [".."],
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
    imports = [".."],
    deps = [
        ":bits",
        ":lib",
    ],
)

py_library(
    name = "window",
    srcs = ["window.py"],
    imports = [".."],
    deps = [
        ":access",
        ":lib",
        ":params",
    ],
)

py_library(
    name = "md_helpers",
    srcs = ["md_helpers.py"],
    imports = [".."],
    deps = [
        ":signal",
    ],
)

py_library(
    name = "gen_cfg_md",
    srcs = ["gen_cfg_md.py"],
    imports = [".."],
    deps = [
        ":ip_block",
        ":md_helpers",
    ],
)

py_library(
    name = "gen_md",
    srcs = ["gen_md.py"],
    imports = [".."],
    deps = [
        ":ip_block",
        ":md_helpers",
        ":multi_register",
        ":reg_block",
        ":register",
        ":window",
    ],
)

py_library(
    name = "gen_cheader",
    srcs = ["gen_cheader.py"],
    imports = [".."],
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
    imports = [".."],
    deps = [
        ":ip_block",
        ":multi_register",
        ":register",
        ":window",
        requirement("mako"),
        requirement("pyyaml"),
        requirement("importlib_resources"),
    ],
)

py_library(
    name = "gen_fpv",
    srcs = ["gen_fpv.py"],
    imports = [".."],
    deps = [
        ":ip_block",
        requirement("mako"),
        requirement("pyyaml"),
        requirement("importlib_resources"),
    ],
)

py_library(
    name = "gen_html",
    srcs = ["gen_html.py"],
    imports = [".."],
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
    imports = [".."],
    deps = [requirement("hjson")],
)

py_library(
    name = "gen_rtl",
    srcs = ["gen_rtl.py"],
    imports = [".."],
    deps = [
        ":ip_block",
        ":lib",
        ":multi_register",
        ":reg_base",
        ":register",
        requirement("mako"),
        requirement("importlib_resources"),
    ],
)

py_library(
    name = "gen_rust",
    srcs = ["gen_rust.py"],
    imports = [".."],
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
    imports = [".."],
    deps = [
        ":field",
        ":ip_block",
        ":multi_register",
        ":params",
        ":register",
        ":signal",
        ":window",
        "//util:version_file",
    ],
)

py_library(
    name = "gen_sec_cm_testplan",
    srcs = ["gen_sec_cm_testplan.py"],
    imports = [".."],
    deps = [
        ":ip_block",
        requirement("hjson"),
        requirement("mako"),
        requirement("importlib_resources"),
    ],
)

py_library(
    name = "gen_selfdoc",
    srcs = ["gen_selfdoc.py"],
    imports = [".."],
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
    imports = [".."],
)

py_library(
    name = "version",
    srcs = ["version.py"],
    imports = [".."],
)

filegroup(
    name = "tpl_files",
    srcs = glob(["**/*.tpl"]),
)
