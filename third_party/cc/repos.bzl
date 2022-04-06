# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@bazel_tools//tools/build_defs/repo:http.bzl", "http_archive")
load("@bazel_tools//tools/build_defs/repo:git.bzl", "git_repository")

def cc_repos():
    git_repository(
        name = "rules_cc",
        commit = "a636005ba28c0344da5110bd8532184c74b6ffdf",
        remote = "https://github.com/bazelbuild/rules_cc.git",
        shallow_since = "1583316607 -0800",
    )

    http_archive(
        name = "com_google_absl",
        strip_prefix = "abseil-cpp-master",
        urls = ["https://github.com/abseil/abseil-cpp/archive/master.zip"],
    )

    native.local_repository(
        name = "googletest",
        path = "sw/vendor/google_googletest",
    )
