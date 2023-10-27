# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_python//python:defs.bzl", "py_library")
load("@ot_python_deps//:requirements.bzl", "requirement")

package(default_visibility = ["//visibility:public"])

py_library(
    name = "topgen",
    srcs = [
        "__init__.py",
        "entropy_buffer_generator.py",
        "gen_top_docs.py",
        "secure_prng.py",
        "strong_random.py",
        "validate.py",
    ],
    deps = [
        ":merge",
        requirement("tabulate"),
        requirement("pycryptodome"),
    ],
)

py_library(
    name = "c_test",
    srcs = ["c_test.py"],
    deps = [
        ":lib",
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
        "//util/reggen:window",
        requirement("mako"),
    ],
)

py_library(
    name = "lib",
    srcs = [
        "c.py",
        "intermodule.py",
        "lib.py",
        "resets.py",
        "rust.py",
    ],
    deps = [
        "//util/reggen:inter_signal",
        "//util/reggen:ip_block",
        "//util/reggen:validate",
        requirement("hjson"),
        requirement("mako"),
    ],
)

py_library(
    name = "merge",
    srcs = [
        "clocks.py",
        "merge.py",
    ],
    deps = [
        ":lib",
        "//util/reggen:params",
    ],
)

filegroup(
    name = "tpl_files",
    srcs = glob(["**/*.tpl"]),
)
