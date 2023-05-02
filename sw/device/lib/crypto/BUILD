# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

package(default_visibility = ["//visibility:public"])

load("//rules:opentitan.bzl", "OPENTITAN_CPU", "OPENTITAN_PLATFORM", "opentitan_binary")

# Top-level cryptolib target.
cc_library(
    name = "otcrypto",
    hdrs = [
        "otcrypto.h",
    ],
    target_compatible_with = [OPENTITAN_CPU],
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
    alwayslink = True,
)
