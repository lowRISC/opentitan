# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@python3//:defs.bzl", "interpreter")
load("@rules_python//python:pip.bzl", "pip_parse")

def tock_deps():
    pip_parse(
        name = "tockloader_deps",
        python_interpreter_target = interpreter,
        requirements_lock = "//:third_party/tock/tockloader_requirements.txt",
    )
