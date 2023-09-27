# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

package(default_visibility = ["//visibility:public"])

load("//rules:opentitan.bzl", "OPENTITAN_CPU")

config_setting(
    name = "crypto_status_debug",
    define_values = {
        "crypto_status_debug": "true",
    },
)

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
        ":status",
        "//sw/device/lib/base:hardened_memory",
        "//sw/device/lib/crypto/drivers:entropy",
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
        "//sw/device/lib/crypto/drivers:entropy",
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
        ":status",
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
        "//sw/device/lib/crypto/drivers:keymgr",
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
        ":status",
        "//sw/device/lib/crypto/impl:drbg",
        "//sw/device/lib/crypto/impl:integrity",
        "//sw/device/lib/crypto/impl:keyblob",
        "//sw/device/lib/crypto/include:datatypes",
    ],
)

cc_test(
    name = "key_transport_unittest",
    srcs = ["key_transport_unittest.cc"],
    deps = [
        ":key_transport",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "rsa",
    srcs = ["rsa.c"],
    hdrs = ["//sw/device/lib/crypto/include:rsa.h"],
    deps = [
        ":integrity",
        ":status",
        "//sw/device/lib/base:hardened_memory",
        "//sw/device/lib/crypto/drivers:entropy",
        "//sw/device/lib/crypto/impl/rsa:rsa_keygen",
        "//sw/device/lib/crypto/impl/rsa:rsa_signature",
        "//sw/device/lib/crypto/include:datatypes",
    ],
)

cc_library(
    name = "status",
    hdrs = [
        "status.h",
    ],
    # Turn debugging on only if the `crypto_status_debug` command-line option
    # is set.
    defines = select({
        ":crypto_status_debug": ["OTCRYPTO_STATUS_DEBUG"],
        "//conditions:default": [],
    }),
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

# Status-code unit tests with debugging information always on.
cc_test(
    name = "status_debug_unittest",
    srcs = ["status_debug_unittest.cc"],
    defines = ["OTCRYPTO_STATUS_DEBUG"],
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
        ":hash",
        ":integrity",
        ":keyblob",
        "//sw/device/lib/base:hardened",
        "//sw/device/lib/crypto/drivers:kmac",
        "//sw/device/lib/crypto/impl/sha2:sha256",
        "//sw/device/lib/crypto/impl/sha2:sha512",
    ],
)
