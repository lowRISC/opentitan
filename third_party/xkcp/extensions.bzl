# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@bazel_tools//tools/build_defs/repo:http.bzl", "http_archive")

xkcp = module_extension(
    implementation = lambda _: _xkcp_repos(),
)

def _xkcp_repos():
    http_archive(
        name = "xkcp",
        build_file = Label("//third_party/xkcp:BUILD.xkcp.bazel"),
        sha256 = "bfd50261e0196988f7c4f45871b82e5ec9c3a74e18276f50dda48ab51f3cdb53",
        # We only need lib of XKCP, so drop everything else except lib
        strip_prefix = "XKCP-56ae09923153c3e801a6891eb19e4a3b5bb6f6e2/lib",
        urls = [
            "https://github.com/XKCP/XKCP/archive/56ae09923153c3e801a6891eb19e4a3b5bb6f6e2.tar.gz",
        ],
        patches = [
            Label("//third_party/xkcp/patches:add_config_header.patch"),
            Label("//third_party/xkcp/patches:add_main_license.patch"),
        ],
        patch_args = ["-p1"],
    )
