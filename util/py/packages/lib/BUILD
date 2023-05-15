# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@ot_python_deps//:requirements.bzl", "requirement")
load("@rules_python//python:defs.bzl", "py_library", "py_test")

package(default_visibility = ["//visibility:public"])

py_library(
    name = "wrapper",
    srcs = [
        "wrapper.py",
    ],
)

py_test(
    name = "wrapper_test",
    srcs = [
        "wrapper_test.py",
    ],
    deps = [
        ":wrapper",
    ],
)

py_library(
    name = "ot_logging",
    srcs = [
        "ot_logging.py",
    ],
    deps = [
        requirement("rich"),
        ":wrapper",
    ],
)

py_test(
    name = "ot_logging_test",
    srcs = [
        "ot_logging_test.py",
    ],
    deps = [
        ":ot_logging",
    ],
)

py_library(
    name = "run",
    srcs = [
        "run.py",
    ],
    deps = [
        ":ot_logging",
    ],
)

py_test(
    name = "run_test",
    srcs = [
        "run_test.py",
    ],
    deps = [
        ":ot_logging",
        ":run",
    ],
)

py_library(
    name = "bazel",
    srcs = [
        "bazel.py",
    ],
    deps = [
        ":run",
    ],
)

py_test(
    name = "bazel_test",
    srcs = [
        "bazel_test.py",
    ],
    deps = [
        ":bazel",
    ],
)
