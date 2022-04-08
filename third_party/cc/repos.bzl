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
        strip_prefix = "abseil-cpp-e854df09dfcb35056c1d42420028648ee0ebebaf",
        url = "https://github.com/abseil/abseil-cpp/archive/e854df09dfcb35056c1d42420028648ee0ebebaf.tar.gz",
    )

    native.local_repository(
        name = "googletest",
        path = "sw/vendor/google_googletest",
    )
