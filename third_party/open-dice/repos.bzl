# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:repo.bzl", "http_archive_or_local")

def open_dice_repos(local = None):
    http_archive_or_local(
        name = "open-dice",
        local = local,
        build_file = Label("//third_party/open-dice:BUILD.open-dice.bazel"),
        strip_prefix = "open-dice-cf3f4cc7a3506a33ee3a437544ef6f40056b3563",
        urls = ["https://github.com/google/open-dice/archive/cf3f4cc7a3506a33ee3a437544ef6f40056b3563.zip"],
        sha256 = "d7ce830111451afe2a255cac3b750f82e50efe2aaf6bac0b076881c964cfe78d",
        patches = [
            Label("//third_party/open-dice:Add-a-local-strlen-implementation.patch"),
        ],
        patch_args = ["-p1"],
    )
