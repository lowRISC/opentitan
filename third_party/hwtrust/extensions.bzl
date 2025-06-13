# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@bazel_tools//tools/build_defs/repo:http.bzl", "http_archive")

hwtrust = module_extension(
    implementation = lambda _: _hwtrust_repos(),
)

def _hwtrust_repos():
    http_archive(
        name = "hwtrust",
        urls = ["https://android.googlesource.com/platform/tools/security/+archive/da7738aaf3ece666272adab6b3091f72ce027e9c.tar.gz"],
        strip_prefix = "remote_provisioning/hwtrust",
        build_file = Label("//third_party/hwtrust:BUILD.hwtrust.bazel"),
    )
