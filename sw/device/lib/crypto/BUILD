# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

package(default_visibility = ["//visibility:public"])

load("//rules/opentitan:defs.bzl", "OPENTITAN_CPU")
load("//rules/opentitan:static_library.bzl", "ot_static_library")
load("@rules_pkg//pkg:mappings.bzl", "pkg_files")
load("@rules_pkg//pkg:tar.bzl", "pkg_tar")

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

cc_import(
    name = "crypto",
    static_library = ":otcrypto",
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        "//sw/device/lib/crypto/include:crypto_hdrs",
    ],
)

pkg_files(
    name = "package",
    srcs = [
        ":otcrypto",
    ],
    prefix = "crypto",
)

pkg_tar(
    name = "cryptolib",
    srcs = [
        ":package",
        "//sw/device/lib/crypto/include:package",
        "//sw/device/lib/crypto/include/freestanding:package",
    ],
    extension = "tar.xz",
)
