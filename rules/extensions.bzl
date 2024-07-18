# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:bitstreams.bzl", "bitstreams_repo")
load("//rules:nonhermetic.bzl", "nonhermetic_repo")

def _bitstreams_impl(ctx):
    bitstreams_repo(name = "bitstreams")

bitstreams = module_extension(
    implementation = _bitstreams_impl,
)

def _nonhermetic_impl(ctx):
    nonhermetic_repo(name = "nonhermetic")

nonhermetic = module_extension(
    implementation = _nonhermetic_impl,
)
