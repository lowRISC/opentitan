# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@//rules:repo.bzl", "http_archive_or_local")

def rust_repos(serde_annotate = None):
    http_archive_or_local(
        name = "lowrisc_serde_annotate",
        local = serde_annotate,
        sha256 = "7300ed093fa3de679512ffdab7d0f1824be2b11f499bb852df29c3ae12e1348d",
        strip_prefix = "serde-annotate-0.0.12",
        url = "https://github.com/lowRISC/serde-annotate/archive/refs/tags/v0.0.12.tar.gz",
    )
