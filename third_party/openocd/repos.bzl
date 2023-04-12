# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:repo.bzl", "http_archive_or_local")

def openocd_repos(local = None):
    OPENOCD_VERSION = "0.12.0"
    http_archive_or_local(
        name = "openocd",
        local = local,
        url = "https://sourceforge.net/projects/openocd/files/openocd/{version}/openocd-{version}.tar.gz".format(version = OPENOCD_VERSION),
        strip_prefix = "openocd-" + OPENOCD_VERSION,
        build_file = "//third_party/openocd:BUILD.openocd.bazel",
        sha256 = "bb367fd19ab96a65ee5b269b60326d9f36bca1c64d9865cc36985d3651aba563",
        patches = [Label("//third_party/openocd:reset_on_dmi_op_error.patch")],
        patch_args = ["-p1"],
    )
