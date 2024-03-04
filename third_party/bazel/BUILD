# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

package(default_visibility = ["//visibility:public"])

load("@rules_proto//proto:defs.bzl", "proto_library")

proto_library(
    name = "duration_proto",
    srcs = ["duration.proto"],
    import_prefix = "google/protobuf",
    # The following works but does not seem to match what the documentation says.
    strip_import_prefix = "",
)

proto_library(
    name = "spawn_proto",
    srcs = ["spawn.proto"],
    deps = [":duration_proto"],
)
