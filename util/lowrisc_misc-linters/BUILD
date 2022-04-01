# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:rules.bzl", "licence_check", "yapf_check")

licence_check(
    name = "licence-check",
    licence = '''
    Copyright lowRISC contributors.
    Licensed under the Apache License, Version 2.0, see LICENSE for details.
    SPDX-License-Identifier: Apache-2.0
    ''',
    exclude_patterns = [".style.yapf"],
)

yapf_check(
    name = "yapf",
    mode = "diff",
)
