# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@bazel_embedded//:bazel_embedded_deps.bzl", _bazel_embedded_deps = "bazel_embedded_deps")
load("@bazel_embedded//platforms:execution_platforms.bzl", "register_platforms")

def bazel_embedded_deps():
    _bazel_embedded_deps()
    register_platforms()
