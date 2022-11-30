# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:repo.bzl", "http_archive_or_local")

def openocd_repos(local = None):
    OPENOCD_VERSION = "0.12.0-rc1"
    http_archive_or_local(
        name = "openocd",
        local = local,
        url = "https://sourceforge.net/projects/openocd/files/openocd/{version}/openocd-{version}.tar.gz".format(version = OPENOCD_VERSION),
        strip_prefix = "openocd-" + OPENOCD_VERSION,
        build_file = "//third_party/openocd:BUILD.openocd.bazel",
        sha256 = "cdd3654a6c2fd046fe766de5ed897d75467138be9b9c271229bbd7409eb902a5",
    )
