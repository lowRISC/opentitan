# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@bazel_tools//tools/build_defs/repo:http.bzl", "http_archive")

def zephyr_repos():
    http_archive(
        name = "zephyr",
        url = "https://github.com/zephyrproject-rtos/zephyr/archive/refs/tags/v3.4.0.tar.gz",
        sha256 = "a066cb7e975f11f1f34d43807965f28ab300625dd0793688c134f4a0e6adbb4b",
        build_file = "//third_party/zephyr:BUILD.zephyr.bazel",
        patch_args = ["-p1"],
        patches = [
            "//third_party/zephyr:0001-devicetree-Remove-unnecessary-deps.patch",
            "//third_party/zephyr:0002-devicetree-Add-interrupt-parent-info-to-generated-he.patch",
        ],
        strip_prefix = "zephyr-3.4.0",
    )

def _zephyr_repo_impl(_mctx):
    zephyr_repos()

zephyr_module_extension = module_extension(
    implementation = _zephyr_repo_impl,
)
