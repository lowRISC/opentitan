# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@bazel_tools//tools/build_defs/repo:http.bzl", "http_archive")

def _doxygen_repos():
    VERSION = "1.13.2"
    UND_VERSION = VERSION.replace(".", "_")

    http_archive(
        name = "doxygen",
        build_file = Label("//third_party/doxygen:BUILD.doxygen.bazel"),
        sha256 = "f2c0a349403bc5b5ade3f501301e32b49ea31b3182666954bc398452fbc0dd1c",
        strip_prefix = "doxygen-" + VERSION,
        urls = [
            "https://github.com/doxygen/doxygen/releases/download/" +
            "Release_{}/doxygen-{}.linux.bin.tar.gz".format(UND_VERSION, VERSION),
        ],
    )

doxygen = module_extension(
    implementation = lambda _: _doxygen_repos(),
)
