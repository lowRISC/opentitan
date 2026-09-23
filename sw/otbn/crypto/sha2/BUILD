# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:otbn.bzl", "otbn_binary", "otbn_library")

package(default_visibility = ["//visibility:public"])

otbn_library(
    name = "sha256_masked",
    srcs = [
        "sha256_masked.s",
    ],
)

otbn_library(
    name = "sha384_masked",
    srcs = [
        "sha384_masked.s",
    ],
)

otbn_library(
    name = "sha512_masked",
    srcs = [
        "sha512_masked.s",
    ],
)

otbn_binary(
    name = "run_sha256",
    srcs = [
        "run_sha256.s",
    ],
    deps = [
        ":sha256_masked",
    ],
)

otbn_binary(
    name = "run_sha384",
    srcs = [
        "run_sha384.s",
    ],
    deps = [
        ":sha384_masked",
    ],
)

otbn_binary(
    name = "run_sha512",
    srcs = [
        "run_sha512.s",
    ],
    deps = [
        ":sha512_masked",
    ],
)
