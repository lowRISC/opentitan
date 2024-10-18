# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

package(default_visibility = ["//visibility:public"])

load("//rules/opentitan:defs.bzl", "OPENTITAN_CPU")

cc_library(
    name = "ecdh_p256",
    srcs = ["ecdh_p256.c"],
    hdrs = ["ecdh_p256.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        ":p256_common",
        "//sw/device/lib/base:hardened",
        "//sw/device/lib/base:hardened_memory",
        "//sw/device/lib/crypto/drivers:otbn",
        "//sw/otbn/crypto:p256_ecdh",
    ],
)

cc_library(
    name = "ecdsa_p256",
    srcs = ["ecdsa_p256.c"],
    hdrs = ["ecdsa_p256.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        ":p256_common",
        "//sw/device/lib/base:hardened",
        "//sw/device/lib/base:hardened_memory",
        "//sw/device/lib/crypto/drivers:otbn",
        "//sw/otbn/crypto:p256_ecdsa",
    ],
)

cc_library(
    name = "p256_common",
    srcs = ["p256_common.c"],
    hdrs = ["p256_common.h"],
    deps = [
        "//sw/device/lib/crypto/drivers:otbn",
        "//sw/device/lib/crypto/impl:status",
    ],
)

cc_library(
    name = "ecdh_p384",
    srcs = ["ecdh_p384.c"],
    hdrs = ["ecdh_p384.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        ":p384_common",
        ":p384_curve_point_valid",
        "//sw/device/lib/base:hardened",
        "//sw/device/lib/base:hardened_memory",
        "//sw/device/lib/crypto/drivers:otbn",
        "//sw/otbn/crypto:p384_ecdh",
    ],
)

cc_library(
    name = "ecdsa_p384",
    hdrs = ["ecdsa_p384.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        ":ecdsa_p384_keygen",
        ":ecdsa_p384_sign",
        ":ecdsa_p384_verify",
    ],
)

cc_library(
    name = "ecdsa_p384_keygen",
    srcs = ["ecdsa_p384_keygen.c"],
    hdrs = ["ecdsa_p384_keygen.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        ":p384_common",
        "//sw/device/lib/base:hardened",
        "//sw/device/lib/base:hardened_memory",
        "//sw/device/lib/crypto/drivers:otbn",
        "//sw/otbn/crypto:p384_ecdsa_keygen",
    ],
)

cc_library(
    name = "ecdsa_p384_sign",
    srcs = ["ecdsa_p384_sign.c"],
    hdrs = ["ecdsa_p384_sign.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        ":p384_common",
        "//sw/device/lib/base:hardened",
        "//sw/device/lib/base:hardened_memory",
        "//sw/device/lib/crypto/drivers:otbn",
        "//sw/otbn/crypto:p384_ecdsa_sign",
    ],
)

cc_library(
    name = "ecdsa_p384_verify",
    srcs = ["ecdsa_p384_verify.c"],
    hdrs = ["ecdsa_p384_verify.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        ":p384_common",
        ":p384_curve_point_valid",
        "//sw/device/lib/base:hardened",
        "//sw/device/lib/base:hardened_memory",
        "//sw/device/lib/crypto/drivers:otbn",
        "//sw/otbn/crypto:p384_ecdsa_verify",
    ],
)

cc_library(
    name = "p384_common",
    srcs = ["p384_common.c"],
    hdrs = ["p384_common.h"],
    deps = [
        "//sw/device/lib/crypto/drivers:otbn",
        "//sw/device/lib/crypto/impl:status",
    ],
)

cc_library(
    name = "p384_curve_point_valid",
    srcs = ["p384_curve_point_valid.c"],
    hdrs = ["p384_curve_point_valid.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        ":p384_common",
        "//sw/device/lib/base:hardened",
        "//sw/device/lib/base:hardened_memory",
        "//sw/device/lib/crypto/drivers:otbn",
        "//sw/otbn/crypto:p384_curve_point_valid",
    ],
)
