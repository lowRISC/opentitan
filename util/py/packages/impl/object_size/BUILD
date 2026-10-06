# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_python//python:defs.bzl", "py_library", "py_test")
load("@ot_python_deps//:requirements.bzl", "requirement")

package(default_visibility = ["//util/py/scripts:__pkg__"])

py_library(
    name = "elf",
    srcs = ["elf.py"],
    deps = [
        ":memory",
        ":types",
        "//util/py/packages/lib:ot_logging",
        requirement("pyelftools"),
    ],
)

py_library(
    name = "memory",
    srcs = ["memory.py"],
    deps = [
        ":types",
    ],
)

py_library(
    name = "report",
    srcs = ["report.py"],
    deps = [
        ":elf",
        ":memory",
        ":types",
        "//util/py/packages/lib:ot_logging",
        requirement("rich"),
    ],
)

py_library(
    name = "types",
    srcs = ["types.py"],
    deps = [
        requirement("rich"),
    ],
)
