# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@bazel_tools//tools/build_defs/repo:http.bzl", "http_archive")

def _host_libs_local_repos_impl(ctx):
    # libusb
    http_archive(
        name = "libusb_src",
        urls = ["https://github.com/libusb/libusb/releases/download/v1.0.27/libusb-1.0.27.tar.bz2"],
        sha256 = "ffaa41d741a8a3bee244ac8e54a72ea05bf2879663c098c82fc5757853441575",
        strip_prefix = "libusb-1.0.27",
        build_file = "//third_party/host_libs:BUILD.libusb.bazel",
    )

    # libftdi1
    http_archive(
        name = "libftdi_src",
        urls = ["https://www.intra2net.com/en/developer/libftdi/download/libftdi1-1.5.tar.bz2"],
        sha256 = "7c7091e9c86196148bd41177b4590dccb1510bfe6cea5bf7407ff194482eb049",
        strip_prefix = "libftdi1-1.5",
        build_file = "//third_party/host_libs:BUILD.libftdi.bazel",
    )

    # libudev-zero
    http_archive(
        name = "libudev_zero_src",
        urls = ["https://github.com/illiliti/libudev-zero/archive/refs/tags/1.0.4.tar.gz"],
        sha256 = "10148cfd6047d387bf71eca72cd19c177084224d96434a118d8def6e0a3d6316",
        strip_prefix = "libudev-zero-1.0.4",
        build_file = "//third_party/host_libs:BUILD.libudev-zero.bazel",
    )

host_libs_local_repos = module_extension(
    implementation = _host_libs_local_repos_impl,
)
