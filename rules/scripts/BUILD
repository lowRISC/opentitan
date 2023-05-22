# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_python//python:defs.bzl", "py_test")
load("@ot_python_deps//:requirements.bzl", "requirement")

package(default_visibility = ["//visibility:public"])

exports_files(glob(["**"]))

py_binary(
    name = "gdb_test_coordinator",
    srcs = [
        "gdb_test_coordinator.py",
    ],
    deps = [
        requirement("typer"),
        requirement("rich"),
    ],
)

py_library(
    name = "bitstreams_workspace",
    srcs = [
        "bitstreams_workspace.py",
    ],
    deps = [
        requirement("jsonschema"),
    ],
)

py_test(
    name = "bitstreams_workspace_test",
    srcs = [
        "bitstreams_workspace_test.py",
    ],
    deps = [
        ":bitstreams_workspace",
    ],
)

sh_binary(
    name = "run_test",
    srcs = ["run_test.sh"],
)
