# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@bazel_tools//tools/build_defs/repo:http.bzl", "http_archive")

def cc_repos():
    http_archive(
        name = "rules_cc",
        sha256 = "123ababe4be661f2fc9189d3b24deabc003926e87d991832cd46b6ae59f7b3c8",
        strip_prefix = "rules_cc-a636005ba28c0344da5110bd8532184c74b6ffdf",
        url = "https://github.com/bazelbuild/rules_cc/archive/a636005ba28c0344da5110bd8532184c74b6ffdf.tar.gz",
    )

    http_archive(
        name = "com_google_absl",
        sha256 = "1da554cf5670fc119ef5afbeb31d10d51e7554df9dced2967663e679b8d852ed",
        strip_prefix = "abseil-cpp-e854df09dfcb35056c1d42420028648ee0ebebaf",
        url = "https://github.com/abseil/abseil-cpp/archive/e854df09dfcb35056c1d42420028648ee0ebebaf.tar.gz",
    )

    http_archive(
        name = "googletest",
        sha256 = "353571c2440176ded91c2de6d6cd88ddd41401d14692ec1f99e35d013feda55a",
        strip_prefix = "googletest-release-1.11.0",
        url = "https://github.com/google/googletest/archive/refs/tags/release-1.11.0.zip",
    )
