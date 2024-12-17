# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@bazel_tools//tools/build_defs/repo:http.bzl", "http_archive")

llvm_compiler_rt = module_extension(
    implementation = lambda _: _llvm_compiler_rt_repos(),
)

def _llvm_compiler_rt_repos():
    http_archive(
        name = "llvm_compiler_rt",
        build_file = Label("//third_party/llvm_compiler_rt:BUILD.llvm_compiler_rt.bazel"),
        sha256 = "46abe68f006646c15f6d551a2be0ac27e681c5fcc646d712389a5e50ddf69c60",
        strip_prefix = "compiler-rt-16.0.2.src",
        urls = [
            "https://github.com/llvm/llvm-project/releases/download/llvmorg-16.0.2/compiler-rt-16.0.2.src.tar.xz",
        ],
        patches = [
            Label("//third_party/llvm_compiler_rt:0001-Headers.patch"),
            Label("//third_party/llvm_compiler_rt:0002-invalid-data.patch"),
        ],
        patch_args = ["-p1"],
    )
