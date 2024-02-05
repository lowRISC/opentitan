# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

package(default_visibility = ["//visibility:public"])

load("//rules/opentitan:static_library.bzl", "ot_static_library")

# Top-level cryptolib target.
ot_static_library(
    name = "otcrypto",
    deps = [
        "//sw/device/lib/crypto/impl:aes",
        "//sw/device/lib/crypto/impl:drbg",
        "//sw/device/lib/crypto/impl:ecc",
        "//sw/device/lib/crypto/impl:hash",
        "//sw/device/lib/crypto/impl:kdf",
        "//sw/device/lib/crypto/impl:key_transport",
        "//sw/device/lib/crypto/impl:mac",
        "//sw/device/lib/crypto/impl:rsa",
        "//sw/device/lib/crypto/include:datatypes",
    ],
)
