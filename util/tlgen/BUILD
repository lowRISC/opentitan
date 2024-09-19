# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_python//python:defs.bzl", "py_library")
load("@ot_python_deps//:requirements.bzl", "requirement")

package(default_visibility = ["//visibility:public"])

py_library(
    name = "tlgen",
    srcs = [
        "__init__.py",
        "doc.py",
        "elaborate.py",
        "generate.py",
        "generate_tb.py",
        "item.py",
        "lib.py",
        "validate.py",
        "xbar.py",
    ],
    deps = [
        "//util/reggen:validate",
        requirement("mako"),
        requirement("importlib_resources"),
    ],
)

filegroup(
    name = "tpl_files",
    srcs = glob(["**/*.tpl"]),
)
