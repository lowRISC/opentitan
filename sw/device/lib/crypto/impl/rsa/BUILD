# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

package(default_visibility = ["//visibility:public"])

load("//rules:opentitan.bzl", "OPENTITAN_CPU")

cc_library(
    name = "rsa_datatypes",
    hdrs = ["rsa_datatypes.h"],
)

cc_library(
    name = "rsa_keygen",
    srcs = ["rsa_keygen.c"],
    hdrs = ["rsa_keygen.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        ":rsa_datatypes",
        "//sw/device/lib/crypto/drivers:otbn",
        "//sw/lib/sw/device/base:hardened",
        "//sw/lib/sw/device/base:hardened_memory",
        "//sw/lib/sw/device/base:memory",
        "//sw/otbn/crypto:run_rsa_keygen",
    ],
)

cc_library(
    name = "rsa_3072_verify",
    srcs = ["rsa_3072_verify.c"],
    hdrs = ["rsa_3072_verify.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        ":rsa_datatypes",
        "//sw/device/lib/crypto/drivers:hmac",
        "//sw/device/lib/crypto/drivers:otbn",
        "//sw/lib/sw/device/base:hardened",
        "//sw/lib/sw/device/base:macros",
        "//sw/lib/sw/device/base:memory",
        "//sw/otbn/crypto:run_rsa_verify_3072",
    ],
)
