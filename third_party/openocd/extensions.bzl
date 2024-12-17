# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@bazel_tools//tools/build_defs/repo:http.bzl", "http_archive")

openocd = module_extension(
    implementation = lambda _: _openocd_repos(),
)

def _openocd_repos():
    OPENOCD_VERSION = "0.12.0"
    http_archive(
        name = "openocd",
        urls = [
            # The sourceforge URL is the canonical one, but the site is not reliable and slow to download.
            # Prefer to use Debian mirror of the tar ball and have sourceforge as backup.
            "https://deb.debian.org/debian/pool/main/o/openocd/openocd_{version}.orig.tar.bz2".format(version = OPENOCD_VERSION),
            "https://sourceforge.net/projects/openocd/files/openocd/{version}/openocd-{version}.tar.gz".format(version = OPENOCD_VERSION),
        ],
        strip_prefix = "openocd-" + OPENOCD_VERSION,
        build_file = "@lowrisc_opentitan//third_party/openocd:BUILD.openocd.bazel",
        sha256 = "af254788be98861f2bd9103fe6e60a774ec96a8c374744eef9197f6043075afa",
        # See Issue(#18087)
        patches = [
            Label("@lowrisc_opentitan//third_party/openocd:calloc_transpose.patch"),
            Label("@lowrisc_opentitan//third_party/openocd:reset_on_dmi_op_error.patch"),
            Label("@lowrisc_opentitan//third_party/openocd:string_truncate_build_error.patch"),
        ],
        patch_args = ["-p1"],
    )
