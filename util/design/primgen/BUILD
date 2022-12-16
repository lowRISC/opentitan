# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_python//python:defs.bzl", "py_binary")
load("@ot_python_deps//:requirements.bzl", "requirement")

package(default_visibility = ["//visibility:public"])

# -o <output_file>
# {-l ..}+
py_binary(
    name = "primgen",
    srcs = ["primgen.py"],
    deps = [
        requirement("mako"),
    ],
)

filegroup(
    name = "tpl_files",
    srcs = glob(["**/*.tpl"]),
)
