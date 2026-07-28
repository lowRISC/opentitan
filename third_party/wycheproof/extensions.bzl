# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@bazel_tools//tools/build_defs/repo:http.bzl", "http_archive")

wycheproof = module_extension(
    implementation = lambda _: _wycheproof_repos(),
)

def _wycheproof_repos():
    http_archive(
        name = "wycheproof",
        build_file = Label("//third_party/wycheproof:BUILD.wycheproof_common.bazel"),
        sha256 = "a257775fafc432e6226710a3beb7cc78728518586d673be22acad1b562815e7d",
        strip_prefix = "wycheproof-1ce52eedab8d4201ff7fddb63fd65b84ff6f12b4",
        url = "https://github.com/lowRISC/wycheproof/archive/1ce52eedab8d4201ff7fddb63fd65b84ff6f12b4.tar.gz",
    )
