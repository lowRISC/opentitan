# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@bazel_tools//tools/build_defs/repo:http.bzl", "http_archive")

freertos = module_extension(
    implementation = lambda _: _freertos_repos(),
)

def _freertos_repos():
    http_archive(
        name = "freertos",
        build_file = Label("//third_party/freertos:BUILD.freertos.bazel"),
        sha256 = "c4c29136071b84841c3f00675da35f5e61e83c1fa18ac43841c478f99190dd7d",
        strip_prefix = "FreeRTOS-Kernel-0b1e9d79c82c1bf00e93142f9d5b1b7b62446995",
        urls = [
            "https://github.com/FreeRTOS/FreeRTOS-Kernel/archive/0b1e9d79c82c1bf00e93142f9d5b1b7b62446995.tar.gz",
        ],
        patches = [
            Label("//third_party/freertos:0001-Remove-mtime-address-macros.patch"),
            Label("//third_party/freertos:0002-Remove-references-to-stdlib.h.patch"),
            Label("//third_party/freertos:0003-Replace-string.h-with-references-to-OT-memory.h.patch"),
        ],
        patch_args = ["-p1"],
    )
