# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@ot_python_deps//:requirements.bzl", "requirement")

py_test(
    name = "device_profile_data_test",
    srcs = [
        "device_profile_data.py",
        "device_profile_data_test.py",
    ],
)

py_test(
    name = "common_test",
    srcs = [
        "common.py",
        "common_test.py",
    ],
)

py_test(
    name = "unittest_coverage_test",
    srcs = [
        "unittest_coverage.py",
        "unittest_coverage_test.py",
    ],
)

py_test(
    name = "functest_coverage_test",
    srcs = [
        "functest_coverage.py",
        "functest_coverage_test.py",
    ],
)

py_test(
    name = "coverage_test",
    srcs = [
        "coverage.py",
        "coverage_test.py",
    ],
    deps = [
        requirement("beautifulsoup4"),
        requirement("typer"),
    ],
)
