# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:repo.bzl", "http_archive_or_local")

def openocd_repos(local = None):
    OPENOCD_VERSION = "0.11.0"
    http_archive_or_local(
        name = "openocd",
        local = local,
        url = "https://sourceforge.net/projects/openocd/files/openocd/{version}/openocd-{version}.tar.gz".format(version = OPENOCD_VERSION),
        strip_prefix = "openocd-" + OPENOCD_VERSION,
        build_file = "//third_party/openocd:BUILD.openocd.bazel",
        sha256 = "242ecb0956d117f79dfec6f807e0ef8c0083e262ff0520f13063f4caa3ad82d9",
    )
