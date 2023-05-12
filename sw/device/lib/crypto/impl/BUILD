# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

package(default_visibility = ["//visibility:public"])

load("//rules:opentitan.bzl", "OPENTITAN_CPU")

cc_library(
    name = "aes",
    srcs = ["aes.c"],
    hdrs = ["//sw/device/lib/crypto/include:aes.h"],
    deps = [
        ":integrity",
        ":keyblob",
        "//sw/device/lib/base:hardened_memory",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/crypto/drivers:aes",
        "//sw/device/lib/crypto/impl/aes_gcm",
        "//sw/device/lib/crypto/include:datatypes",
    ],
)

cc_library(
    name = "drbg",
    srcs = ["drbg.c"],
    hdrs = ["//sw/device/lib/crypto/include:drbg.h"],
    deps = [
        "//sw/device/lib/crypto/include:datatypes",
    ],
)

cc_library(
    name = "ecc",
    srcs = ["ecc.c"],
    hdrs = ["//sw/device/lib/crypto/include:ecc.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        ":keyblob",
        "//sw/device/lib/crypto/drivers:hmac",
        "//sw/device/lib/crypto/impl/ecc:ecdh_p256",
        "//sw/device/lib/crypto/impl/ecc:ecdsa_p256",
        "//sw/device/lib/crypto/include:datatypes",
    ],
)

cc_library(
    name = "hash",
    srcs = ["hash.c"],
    hdrs = [
        "//sw/device/lib/crypto/include:hash.h",
    ],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        ":status",
        "//sw/device/lib/base:hardened",
        "//sw/device/lib/crypto/drivers:hmac",
        "//sw/device/lib/crypto/drivers:kmac",
        "//sw/device/lib/crypto/impl/sha2:sha256",
        "//sw/device/lib/crypto/impl/sha2:sha512",
        "//sw/device/lib/crypto/include:datatypes",
    ],
)

cc_library(
    name = "integrity",
    srcs = ["integrity.c"],
    hdrs = ["integrity.h"],
    deps = [
        "//sw/device/lib/base:hardened",
        "//sw/device/lib/crypto/include:datatypes",
    ],
)

cc_library(
    name = "kdf",
    srcs = ["kdf.c"],
    hdrs = ["//sw/device/lib/crypto/include:kdf.h"],
    deps = [
        "//sw/device/lib/crypto/include:datatypes",
    ],
)

cc_library(
    name = "keyblob",
    srcs = ["keyblob.c"],
    hdrs = ["keyblob.h"],
    deps = [
        ":integrity",
        ":status",
        "//sw/device/lib/base:hardened_memory",
        "//sw/device/lib/crypto/include:datatypes",
    ],
)

cc_test(
    name = "keyblob_unittest",
    srcs = ["keyblob_unittest.cc"],
    deps = [
        ":keyblob",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "key_transport",
    srcs = ["key_transport.c"],
    hdrs = ["//sw/device/lib/crypto/include:key_transport.h"],
    deps = [
        "//sw/device/lib/crypto/include:datatypes",
    ],
)

cc_library(
    name = "rsa",
    srcs = ["rsa.c"],
    hdrs = ["//sw/device/lib/crypto/include:rsa.h"],
    deps = [
        "//sw/device/lib/crypto/include:datatypes",
    ],
)

cc_library(
    name = "status",
    srcs = ["status.c"],
    hdrs = [
        "status.h",
    ],
    deps = [
        "//sw/device/lib/base:status",
        "//sw/device/lib/crypto/include:datatypes",
    ],
)

cc_test(
    name = "status_unittest",
    srcs = ["status_unittest.cc"],
    deps = [
        ":status",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "mac",
    srcs = ["mac.c"],
    hdrs = [
        "//sw/device/lib/crypto/include:mac.h",
    ],
    deps = [
        ":integrity",
        ":keyblob",
        "//sw/device/lib/base:hardened",
        "//sw/device/lib/crypto/drivers:kmac",
        "//sw/device/lib/crypto/impl/sha2:sha256",
    ],
)
