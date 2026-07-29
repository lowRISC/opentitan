# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_python//python:defs.bzl", "py_library")
load("@ot_python_deps//:requirements.bzl", "requirement")

package(default_visibility = ["//visibility:public"])

py_library(
    name = "topgen",
    srcs = [
        "__init__.py",
        "gen_top_docs.py",
        "validate.py",
    ],
    deps = [
        ":c",
        ":lib",
        ":merge",
        ":rust",
        ":secure_prng",
        "//util/reggen:ip_block",
        "//util/reggen:validate",
        requirement("tabulate"),
        requirement("pycryptodome"),
    ],
)

py_library(
    name = "c_test",
    srcs = ["c_test.py"],
    deps = [
        ":c",
        ":lib",
        "//util/reggen:interrupt",
        "//util/reggen:ip_block",
    ],
)

py_library(
    name = "gen_dv",
    srcs = [
        "gen_dv.py",
        "top.py",
    ],
    deps = [
        "//util/reggen:gen_dv",
        "//util/reggen:ip_block",
        "//util/reggen:params",
        "//util/reggen:reg_block",
        "//util/reggen:window",
        requirement("mako"),
        requirement("importlib_resources"),
    ],
)

py_library(
    name = "lib",
    srcs = [
        "intermodule.py",
        "lib.py",
    ],
    deps = [
        "//util/reggen:inter_signal",
        "//util/reggen:ip_block",
        "//util/reggen:validate",
        requirement("hjson"),
    ],
)

py_library(
    name = "c",
    srcs = ["c.py"],
    deps = [
        ":lib",
        "//util/reggen:ip_block",
        requirement("mako"),
    ],
)

py_library(
    name = "rust",
    srcs = ["rust.py"],
    deps = [
        ":lib",
        "//util:version_file",
        "//util/reggen:ip_block",
        requirement("mako"),
    ],
)

py_library(
    name = "clocks",
    srcs = ["clocks.py"],
    deps = [
        ":lib",
    ],
)

py_library(
    name = "resets",
    srcs = ["resets.py"],
    deps = [
        ":clocks",
    ],
)

py_library(
    name = "secure_prng",
    srcs = ["secure_prng.py"],
    deps = [
        requirement("pycryptodome"),
    ],
)

py_library(
    name = "merge",
    srcs = ["merge.py"],
    deps = [
        ":c",
        ":clocks",
        ":lib",
        ":resets",
        ":secure_prng",
        "//util/reggen:ip_block",
        "//util/reggen:params",
    ],
)

filegroup(
    name = "tpl_files",
    srcs = glob(["**/*.tpl"]),
)
