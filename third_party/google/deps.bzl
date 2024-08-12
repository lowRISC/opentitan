# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_pkg//:deps.bzl", "rules_pkg_dependencies")
load("@rules_foreign_cc//foreign_cc:repositories.bzl", "rules_foreign_cc_dependencies")

def google_deps():
    rules_pkg_dependencies()

    # Finish setting up rules_foreign_cc, per instructions:
    # https://bazelbuild.github.io/rules_foreign_cc/0.9.0/index.html
    rules_foreign_cc_dependencies()
