# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_fuzzing//fuzzing:repositories.bzl", "rules_fuzzing_dependencies")
load("@rules_fuzzing//fuzzing:init.bzl", "rules_fuzzing_init")

def fuzzing_deps():
    rules_fuzzing_dependencies()
    rules_fuzzing_init()
