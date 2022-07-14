# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_python//python:defs.bzl", "py_binary")

package(default_visibility = ["//visibility:public"])

exports_files(glob(["**"]))

py_test(
    name = "bitstreams_workspace_test",
    srcs = [
        "bitstreams_workspace.py",
        "bitstreams_workspace_test.py",
    ],
)
