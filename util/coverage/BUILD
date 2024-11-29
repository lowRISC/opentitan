# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@ot_python_deps//:requirements.bzl", "requirement")

py_library(
    name = "device_profile_data",
    srcs = ["device_profile_data.py"],
    imports = ["."],
)

py_library(
    name = "common",
    srcs = ["common.py"],
    imports = ["."],
)

py_library(
    name = "unittest_coverage",
    srcs = ["unittest_coverage.py"],
    imports = ["."],
    deps = [":common"],
)

py_library(
    name = "functest_coverage",
    srcs = ["functest_coverage.py"],
    imports = ["."],
    deps = [
        ":common",
        ":device_profile_data",
    ],
)

py_library(
    name = "coverage",
    srcs = ["coverage.py"],
    imports = ["."],
    deps = [
        ":combined_report",
        ":common",
        ":functest_coverage",
        ":unittest_coverage",
    ],
)

py_library(
    name = "combined_report",
    srcs = ["combined_report.py"],
    imports = ["."],
)

py_test(
    name = "device_profile_data_test",
    srcs = ["device_profile_data_test.py"],
    deps = [":device_profile_data"],
)

py_test(
    name = "common_test",
    srcs = ["common_test.py"],
    deps = [":common"],
)

py_test(
    name = "unittest_coverage_test",
    srcs = ["unittest_coverage_test.py"],
    deps = [":unittest_coverage"],
)

py_test(
    name = "functest_coverage_test",
    srcs = ["functest_coverage_test.py"],
    deps = [":functest_coverage"],
)

py_test(
    name = "coverage_test",
    srcs = ["coverage_test.py"],
    deps = [
        ":coverage",
        requirement("beautifulsoup4"),
        requirement("typer"),
    ],
)
