# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

package(default_visibility = ["//visibility:public"])

load("//rules:opentitan.bzl", "OPENTITAN_CPU")

cc_library(
    name = "ecdsa_p256",
    srcs = ["ecdsa_p256.c"],
    hdrs = ["ecdsa_p256.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        "//sw/device/lib/base:hardened",
        "//sw/device/lib/crypto/drivers:otbn",
        "//sw/otbn/crypto:p256_ecdsa",
    ],
)
