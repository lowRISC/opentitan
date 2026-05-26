# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@bazel_tools//tools/build_defs/repo:http.bzl", "http_archive")

hsm = module_extension(
    implementation = lambda _: _hsm_repos(),
)

def _hsm_repos():
    http_archive(
        name = "softhsm2",
        build_file = Label("//third_party/hsm:BUILD.softhsm2.bazel"),
        url = "https://github.com/softhsm/SoftHSMv2/archive/02cebd57b12a2c0a22b15c4a4d19e40f9fc2de6b.tar.gz",
        strip_prefix = "SoftHSMv2-02cebd57b12a2c0a22b15c4a4d19e40f9fc2de6b",
        sha256 = "92a6ad6ff2adaf9204c7f848fee925a7cf32113f30cbe2807a94e91a9c279bc7",
        patches = [
            Label("//third_party/hsm/patches:0001-Disable-filename-logging.patch"),
            Label("//third_party/hsm/patches:0002-slh-dsa.patch"),
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
    http_archive(
        name = "opensc",
        build_file = Label("//third_party/hsm:BUILD.opensc.bazel"),
        url = "https://github.com/OpenSC/OpenSC/archive/refs/tags/0.26.0.tar.gz",
        strip_prefix = "OpenSC-0.26.0",
        sha256 = "c692ac7639fa398f7f07b1070ea5358344000d49d08dcb825296d4cec94c6b1f",
    )
    http_archive(
        name = "cloud_kms_hsm",
        build_file = Label("//third_party/hsm:BUILD.cloud_kms_hsm.bazel"),
        url = "https://github.com/GoogleCloudPlatform/kms-integrations/releases/download/pkcs11-v1.8/libkmsp11-1.8-linux-amd64.tar.gz",
        strip_prefix = "libkmsp11-1.8-linux-amd64",
        sha256 = "3b932f22a8abb631442c3276e9c309554c81855526b74fbc9edaddcb57a557f7",
    )
