# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@bazel_tools//tools/build_defs/repo:http.bzl", "http_archive")

serde_annotate = module_extension(
    implementation = lambda _: _serde_annotate_repo(),
)

def _serde_annotate_repo():
    http_archive(
        name = "lowrisc_serde_annotate",
        integrity = "sha256-E/hy/AxZ6uPJyh5R17krKDGPTdGAOKZ5ZkomBetg4iI=",
        strip_prefix = "serde-annotate-23a125e7614815d193be23b43858635f95f58120",
        url = "https://github.com/lowRISC/serde-annotate/archive/23a125e7614815d193be23b43858635f95f58120.tar.gz",
    )
