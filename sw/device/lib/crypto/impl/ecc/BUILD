# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

package(default_visibility = ["//visibility:public"])

load("//rules/opentitan:defs.bzl", "OPENTITAN_CPU")

cc_library(
    name = "p256",
    srcs = ["p256.c"],
    hdrs = ["p256.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        "//sw/device/lib/base:hardened",
        "//sw/device/lib/base:hardened_memory",
        "//sw/device/lib/crypto/drivers:otbn",
        "//sw/device/lib/crypto/drivers:rv_core_ibex",
        "//sw/device/lib/crypto/impl:status",
        "//sw/otbn/crypto:run_p256",
    ],
)

cc_library(
    name = "p384",
    srcs = ["p384.c"],
    hdrs = ["p384.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        "//sw/device/lib/base:hardened",
        "//sw/device/lib/base:hardened_memory",
        "//sw/device/lib/crypto/drivers:otbn",
        "//sw/device/lib/crypto/drivers:rv_core_ibex",
        "//sw/device/lib/crypto/impl:status",
        "//sw/otbn/crypto:run_p384",
    ],
)
