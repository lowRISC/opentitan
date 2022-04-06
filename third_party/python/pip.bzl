# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_python//python:pip.bzl", "pip_install")
load("@python3//:defs.bzl", "interpreter")

def pip_deps():
    pip_install(
        name = "ot_python_deps",
        python_interpreter_target = interpreter,
        requirements = "//:python-requirements.txt",
    )
