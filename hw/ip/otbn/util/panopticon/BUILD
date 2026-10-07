# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_python//python:defs.bzl", "py_binary", "py_library", "py_test")

package(default_visibility = ["//visibility:public"])

py_library(
    name = "aggregate_lib",
    srcs = [
        "__init__.py",
        "aggregate.py",
    ],
    data = ["viewer.html"],
    imports = [
        "..",
        "../../dv/otbnsim",
    ],
    deps = [
        "//hw/ip/otbn/util:otbn_fi_campaign",
        "//hw/ip/otbn/util:otbn_tvla_campaign",
        "//hw/ip/otbn/util/shared:toolchain",
    ],
)

py_binary(
    name = "aggregate",
    srcs = ["aggregate.py"],
    data = ["viewer.html"],
    deps = [":aggregate_lib"],
)

py_test(
    name = "aggregate_test",
    srcs = ["aggregate_test.py"],
    deps = [":aggregate_lib"],
)
