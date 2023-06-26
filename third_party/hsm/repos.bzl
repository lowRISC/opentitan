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
    http_archive(
        name = "sc_hsm",
        build_file = Label("//third_party/hsm:BUILD.sc_hsm.bazel"),
        url = "https://github.com/CardContact/sc-hsm-embedded/archive/refs/tags/V2.12.tar.gz",
        strip_prefix = "sc-hsm-embedded-2.12",
        sha256 = "707fca9df630708e0e59a7d4a8a7a016c56c83a585957f0fd9f806c0762f1944",
    )
