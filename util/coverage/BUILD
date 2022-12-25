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
    name = "coverage_off_target_test",
    srcs = [
        "coverage_off_target.py",
        "coverage_off_target_test.py",
    ],
    deps = [
        requirement("typer"),
    ],
)
