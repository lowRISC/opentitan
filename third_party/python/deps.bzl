# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_python//python:repositories.bzl", "py_repositories", "python_register_toolchains")

def python_deps():
    py_repositories()
    python_register_toolchains(
        name = "python3",
        python_version = "3.9",
        ignore_root_user_error = True,
    )
