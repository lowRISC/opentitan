# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load(
    "@io_bazel_rules_go//go:deps.bzl",
    "go_download_sdk",
    "go_rules_dependencies",
)
load("@bazel_gazelle//:deps.bzl", "gazelle_dependencies")

def go_deps():
    go_download_sdk(
        name = "go_sdk",
        version = "1.19.1",
        sdks = {
            # NOTE: In most cases the whole sdks attribute is not needed. We use
            # it to avoid the dependency on the index file for the
            # SHA-256 checksums, which is downloaded via a `ctx.download` action
            # which does not seem to cache files in the repository cache like
            # the `ctx.download_and_extract` action does. Therefore, we avoid
            # relying on `rules_go` to download the version and get the expected
            # filenames and checksums from https://go.dev/dl/ manually.
            "linux_amd64": (
                "go1.19.1.linux-amd64.tar.gz",
                "acc512fbab4f716a8f97a8b3fbaa9ddd39606a28be6c2515ef7c6c6311acffde",
            ),
            "linux_arm64": (
                "go1.19.1.linux-arm64.tar.gz",
                "49960821948b9c6b14041430890eccee58c76b52e2dbaafce971c3c38d43df9f",
            ),
            "darwin_amd64": (
                "go1.19.1.darwin-amd64.tar.gz",
                "b2828a2b05f0d2169afc74c11ed010775bf7cf0061822b275697b2f470495fb7",
            ),
            "darwin_arm64": (
                "go1.19.1.darwin-arm64.tar.gz",
                "e46aecce83a9289be16ce4ba9b8478a5b89b8aa0230171d5c6adbc0c66640548",
            ),
        },
    )
    go_rules_dependencies()
    gazelle_dependencies()
