# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@bazel_tools//tools/build_defs/repo:http.bzl", "http_archive")

def python_repos():
    http_archive(
        name = "rules_python",
        sha256 = "9e9a58cff49f80afd1c9fcc7137b719531f7a7427cce4fda1d30ca27b4a46a8a",
        strip_prefix = "rules_python-07c3f8547abbd5b97839a48af226a0fbcfaa5e7c",
        url = "https://github.com/lowRISC/rules_python/archive/07c3f8547abbd5b97839a48af226a0fbcfaa5e7c.tar.gz",
    )
