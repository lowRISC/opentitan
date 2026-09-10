# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@bazel_tools//tools/build_defs/repo:http.bzl", "http_archive")

serde_annotate = module_extension(
    implementation = lambda _: _serde_annotate_repo(),
)

def _serde_annotate_repo():
    http_archive(
        name = "lowrisc_serde_annotate",
        integrity = "sha256-pT+WAj/aVJADXzwHjNmKXIDh+7yWiy8ti8dENmDb7z4=",
        strip_prefix = "serde-annotate-0.0.13",
        url = "https://github.com/lowRISC/serde-annotate/archive/refs/tags/v0.0.13.tar.gz",
    )

# Provides the `libclang` (plus a `clang` binary and C++ runtime) that the
# rules_rust bindgen toolchain loads. By default these come from the prebuilt
# LLVM release Bazel downloads (@llvm_toolchain_llvm). Under Nix that libclang
# cannot be dlopen'd -- bindgen-cli uses the nixpkgs glibc loader, which ignores
# /etc/ld.so.cache and resolves a dlopen'd library's needs only via its RUNPATH,
# and the release libclang has RUNPATH `$ORIGIN/../lib` so it can't find
# libtinfo.so.5 / libstdc++.so.6. When the `OT_BINDGEN_LLVM` environment
# variable points at a nixpkgs libclang tree (see lowrisc-nix bindgen-libclang,
# wired up by the lint FHS), we use that instead: its libclang.so carries an
# absolute nix-store RUNPATH and resolves its own dependencies.
def _bindgen_llvm_impl(rctx):
    nix_tree = rctx.os.environ.get("OT_BINDGEN_LLVM", "")
    if nix_tree:
        rctx.symlink(nix_tree + "/bin/clang", "bin/clang")
        rctx.symlink(nix_tree + "/lib/libclang.so", "lib/libclang.so")
        rctx.symlink(nix_tree + "/lib/libc++.so", "lib/libc++.so")
    else:
        rctx.symlink(rctx.path(Label("@llvm_toolchain_llvm//:bin/clang")), "bin/clang")
        rctx.symlink(rctx.path(Label("@llvm_toolchain_llvm//:lib/libclang.so")), "lib/libclang.so")
        rctx.symlink(rctx.path(Label("@llvm_toolchain_llvm//:lib/libc++.so")), "lib/libc++.so")
    rctx.file("BUILD.bazel", 'exports_files(["bin/clang", "lib/libclang.so", "lib/libc++.so"])\n')

_bindgen_llvm_repo = repository_rule(
    implementation = _bindgen_llvm_impl,
    # Refetch when the Nix-provided tree changes (or appears/disappears).
    environ = ["OT_BINDGEN_LLVM"],
)

bindgen_llvm = module_extension(
    implementation = lambda _: _bindgen_llvm_repo(name = "bindgen_llvm"),
)
