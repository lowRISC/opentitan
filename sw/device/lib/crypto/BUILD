# Copyright lowRISC contributors (OpenTitan project).
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

# This library imports the archive created by the static library rule
# above. This can be used within the codebase to test the cryptolib
# as built.
cc_import(
    name = "crypto",
    static_library = ":otcrypto",
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        "//sw/device/lib/crypto/include:crypto_hdrs",
    ],
)

# This library imports the archive created by the static library rule
# above AND provides the header files as though they'd been exported
# from the repo in the same way as the packaged headers in the
# cryptolib.tar.xz output below.  This is used to create tests that
# verify the exported library and header files work correctly when
# exported.  Because we export a version of the `hardended_bool_t` and
# `status_t` types, it can be somewhat difficult to use this target
# within the repo (ie: you cannot use the in-repo definitions of those
# types, nor can you directly use anything that depends on those types).
# See //sw/device/test/crypto:otcrypto_export_test as an example.
cc_import(
    name = "crypto_exported_for_test",
    static_library = ":otcrypto",
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        "//sw/device/lib/crypto/include:exported_headers_for_test",
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
