# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_python//python:pip.bzl", "pip_parse")

def pip_deps():
    pip_parse(
        name = "ot_python_deps",
        python_interpreter_target = "@python3_host//:python",
        requirements_lock = "@lowrisc_opentitan//:python-requirements.txt",
    )
