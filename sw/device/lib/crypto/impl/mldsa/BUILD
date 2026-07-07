# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

package(default_visibility = ["//visibility:public"])

load("//rules/opentitan:defs.bzl", "OPENTITAN_CPU")

cc_library(
    name = "mldsa",
    srcs = ["mldsa.c"],
    hdrs = ["mldsa.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        "//sw/device/lib/base:hardened",
        "//sw/device/lib/base:hardened_memory",
        "//sw/device/lib/crypto/drivers:otbn",
        "//sw/device/lib/crypto/impl:status",
        "//sw/otbn/crypto/mldsa87/sign:mldsa87_sign",
        "//sw/otbn/crypto/mldsa87/verify:mldsa87_verify",
    ],
)
