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
        "//sw/device/lib/base:hardened",
        "//sw/device/lib/base:hardened_memory",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/crypto/drivers:otbn",
        "//sw/otbn/crypto:run_rsa_keygen",
    ],
)

cc_library(
    name = "rsa_modexp",
    srcs = ["rsa_modexp.c"],
    hdrs = ["rsa_modexp.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        ":rsa_datatypes",
        "//sw/device/lib/crypto/drivers:otbn",
        "//sw/otbn/crypto:run_rsa_modexp",
    ],
)

cc_library(
    name = "rsa_padding",
    srcs = ["rsa_padding.c"],
    hdrs = ["rsa_padding.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        ":rsa_datatypes",
        "//sw/device/lib/base:hardened",
        "//sw/device/lib/base:hardened_memory",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/crypto/impl:hash",
        "//sw/device/lib/crypto/impl:status",
        "//sw/device/lib/crypto/impl/sha2:sha256",
        "//sw/device/lib/crypto/impl/sha2:sha512",
    ],
)

cc_library(
    name = "rsa_signature",
    srcs = ["rsa_signature.c"],
    hdrs = ["rsa_signature.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        ":rsa_datatypes",
        ":rsa_modexp",
        ":rsa_padding",
        "//sw/device/lib/base:hardened",
        "//sw/device/lib/base:hardened_memory",
        "//sw/device/lib/base:math",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/crypto/drivers:entropy",
        "//sw/device/lib/crypto/impl:hash",
        "//sw/device/lib/crypto/impl/sha2:sha256",
        "//sw/device/lib/crypto/impl/sha2:sha512",
    ],
)

cc_library(
    name = "rsa_3072_verify",
    srcs = ["rsa_3072_verify.c"],
    hdrs = ["rsa_3072_verify.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        ":rsa_datatypes",
        "//sw/device/lib/base:hardened",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/crypto/drivers:hmac",
        "//sw/device/lib/crypto/drivers:otbn",
        "//sw/otbn/crypto:run_rsa_verify_3072",
    ],
)
