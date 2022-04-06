# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_python//python:repositories.bzl", "python_register_toolchains")

def python_deps():
    python_register_toolchains(
        name = "python3",
        python_version = "3.9",
    )
