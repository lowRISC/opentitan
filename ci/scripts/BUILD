# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_python//python:defs.bzl", "py_test")

sh_binary(
    name = "run_test",
    srcs = ["run_test.sh"],
)

py_test(
    name = "check_pr_changes_allowed_test",
    srcs = ["check_pr_changes_allowed_test.py"],
    data = ["check-pr-changes-allowed.py"],
)
