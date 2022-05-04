# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@cargo_raze//:repositories.bzl", "cargo_raze_repositories")

def raze_deps():
    cargo_raze_repositories()
