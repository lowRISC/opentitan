# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:repo.bzl", "http_archive_or_local")

def raze_repos(local = None):
    http_archive_or_local(
        name = "cargo_raze",
        local = local,
        strip_prefix = "cargo-raze-0.15.0",
        url = "https://github.com/google/cargo-raze/archive/v0.15.0.tar.gz",
        sha256 = "58ecdbae2680b71edc19a0f563cdb73e66c8914689b6edab258c8b90a93b13c7",
        patches = [
            Label("//third_party/cargo_raze:pr-481-libssh2-pkgconfig.patch"),
            Label("//third_party/cargo_raze:pr-488-c11-fixes.patch"),
            Label("//third_party/cargo_raze:pr-491-local-paths.patch"),
            Label("//third_party/cargo_raze:pr-492-skip-submodules.patch"),
        ],
        patch_args = ["-p1"],
    )
