# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@bazel_tools//tools/build_defs/repo:git.bzl", "new_git_repository")

def freertos_deps():
    new_git_repository(
        name = "freertos",
        build_file = Label("//third_party/freertos:BUILD.freertos.bazel"),
        remote = "https://github.com/FreeRTOS/FreeRTOS-Kernel.git",
        commit = "0b1e9d79c82c1bf00e93142f9d5b1b7b62446995",
        shallow_since = "1628817357 -0700",
        patches = [
            Label("//third_party/freertos:0001-Remove-mtime-address-macros.patch"),
            Label("//third_party/freertos:0002-Remove-references-to-stdlib.h.patch"),
            Label("//third_party/freertos:0003-Replace-string.h-with-references-to-OT-memory.h.patch"),
        ],
        patch_args = ["-p1"],
    )
