# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@lowrisc_lint//rules:deps.bzl", "lowrisc_misc_linters_dependencies")
load("@lowrisc_lint//rules:pip.bzl", "lowrisc_misc_linters_pip_dependencies")

def lint_deps():
    lowrisc_misc_linters_dependencies()
    lowrisc_misc_linters_pip_dependencies()
