# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

package(default_visibility = ["//visibility:public"])

load("//rules:opentitan.bzl", "OPENTITAN_CPU")

cc_library(
    name = "sha256",
    srcs = ["sha256.c"],
    hdrs = ["sha256.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        "//sw/device/lib/crypto/drivers:otbn",
        "//sw/lib/sw/device/base:hardened",
        "//sw/lib/sw/device/base:hardened_memory",
        "//sw/lib/sw/device/base:macros",
        "//sw/lib/sw/device/base:memory",
        "//sw/otbn/crypto:run_sha256",
    ],
)

cc_library(
    name = "sha512",
    srcs = ["sha512.c"],
    hdrs = ["sha512.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        "//sw/device/lib/crypto/drivers:otbn",
        "//sw/lib/sw/device/base:hardened",
        "//sw/lib/sw/device/base:hardened_memory",
        "//sw/lib/sw/device/base:macros",
        "//sw/lib/sw/device/base:memory",
        "//sw/otbn/crypto:run_sha512",
    ],
)
