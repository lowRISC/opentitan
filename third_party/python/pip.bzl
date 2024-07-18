# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_python//python:pip.bzl", "pip_parse")
load("@python3//:defs.bzl", "interpreter")

def pip_deps():
    pip_parse(
        name = "ot_python_deps",
        python_interpreter_target = interpreter,
        requirements_lock = "//:python-requirements.txt",
    )
