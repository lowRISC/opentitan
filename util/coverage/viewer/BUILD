# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_python//python:defs.bzl", "py_binary", "py_library", "py_test")

package(default_visibility = ["//visibility:public"])

py_library(
    name = "lcov",
    srcs = ["lcov.py"],
)

py_test(
    name = "lcov_test",
    srcs = ["lcov_test.py"],
    deps = [":lcov"],
)

py_library(
    name = "coverage_data",
    srcs = ["coverage_data.py"],
)

py_test(
    name = "coverage_data_test",
    srcs = ["coverage_data_test.py"],
    deps = [
        ":coverage_data",
        ":lcov",
    ],
)

py_library(
    name = "collect_lib",
    srcs = ["collect.py"],
    deps = [
        ":coverage_data",
        ":lcov",
    ],
)

py_binary(
    name = "collect",
    srcs = ["collect.py"],
    deps = [
        ":collect_lib",
        ":coverage_data",
        ":lcov",
    ],
)

py_test(
    name = "collect_test",
    srcs = ["collect_test.py"],
    deps = [
        ":collect_lib",
        ":coverage_data",
        ":lcov",
    ],
)

py_binary(
    name = "bundler",
    srcs = ["bundler.py"],
    data = ["viewer.html"],
)

py_test(
    name = "bundler_test",
    srcs = ["bundler_test.py"],
    deps = [":bundler"],
)
