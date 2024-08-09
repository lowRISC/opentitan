# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//third_party/tock:repos.bzl", "tock_repos")

def _tock_impl(ctx):
    tock_repos()

tock = module_extension(
    implementation = _tock_impl,
)
