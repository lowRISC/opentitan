# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@bazel_tools//tools/build_defs/repo:http.bzl", "http_archive")

def hsm_repos():
    http_archive(
        name = "softhsm2",
        build_file = Label("//third_party/hsm:BUILD.softhsm2.bazel"),
        url = "https://github.com/opendnssec/SoftHSMv2/archive/4975c0df4c7090e97a3860ae21079a9597cfedc6.tar.gz",
        strip_prefix = "SoftHSMv2-4975c0df4c7090e97a3860ae21079a9597cfedc6",
        sha256 = "72cf979ec4f74ca4555861dcae45cf7d1b667cc2e4f3ee3fb26e6ff1b99aec95",
        patches = [
            Label("//third_party/hsm:0001-Disable-filename-logging.patch"),
        ],
        patch_args = ["-p1"],
    )
