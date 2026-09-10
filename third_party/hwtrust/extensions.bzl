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
        urls = [
            # Use lowrisc cache due to rate limiting on the original URL
            "https://storage.googleapis.com/lowrisc-ci-longterm-cache/security-da7738aaf3ece666272adab6b3091f72ce027e9c.tar.gz",
            # "https://android.googlesource.com/platform/tools/security/+archive/da7738aaf3ece666272adab6b3091f72ce027e9c.tar.gz"
        ],
        strip_prefix = "remote_provisioning/hwtrust",
        build_file = Label("//third_party/hwtrust:BUILD.hwtrust.bazel"),
        sha256 = "d7e0bb13224294c69e8a5642464d7d7048402c52f7ee9050fb8a85acf01b0837",
    )
