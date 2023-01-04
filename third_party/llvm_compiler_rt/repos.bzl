# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@bazel_tools//tools/build_defs/repo:http.bzl", "http_archive")

def llvm_compiler_rt_repos():
    http_archive(
        name = "llvm_compiler_rt",
        build_file = Label("//third_party/llvm_compiler_rt:BUILD.llvm_compiler_rt.bazel"),
        sha256 = "7b33955031f9a9c5d63077dedb0f99d77e4e7c996266952c1cec55626dca5dfc",
        strip_prefix = "compiler-rt-13.0.1.src",
        urls = [
            "https://github.com/llvm/llvm-project/releases/download/llvmorg-13.0.1/compiler-rt-13.0.1.src.tar.xz",
        ],
        patches = [
            Label("//third_party/llvm_compiler_rt:0001-Headers.patch"),
        ],
        patch_args = ["-p1"],
    )
