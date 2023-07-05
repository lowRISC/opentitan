# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_pkg//:deps.bzl", "rules_pkg_dependencies")
load("@rules_foreign_cc//foreign_cc:repositories.bzl", "rules_foreign_cc_dependencies")
load("@rules_fuzzing//fuzzing:repositories.bzl", "rules_fuzzing_dependencies")
load("@rules_fuzzing//fuzzing:init.bzl", "rules_fuzzing_init")

def google_deps():
    rules_pkg_dependencies()

    # Finish setting up rules_foreign_cc, per instructions:
    # https://bazelbuild.github.io/rules_foreign_cc/0.9.0/index.html
    rules_foreign_cc_dependencies()

    rules_fuzzing_dependencies()
    rules_fuzzing_init()
