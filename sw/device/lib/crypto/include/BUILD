# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

package(default_visibility = ["//visibility:public"])

load("@rules_pkg//pkg:mappings.bzl", "pkg_files")

# Export all headers.
exports_files(glob(["*.h"]))

cc_library(
    name = "datatypes",
    hdrs = ["datatypes.h"],
    defines = ["OTCRYPTO_IN_REPO=1"],
    includes = ["."],
    deps = [
        "//sw/device/lib/base:hardened",
        "//sw/device/lib/base:status",
    ],
)

cc_library(
    name = "crypto_hdrs",
    hdrs = [
        "aes.h",
        "aes_gcm.h",
        "datatypes.h",
        "drbg.h",
        "ecc_p256.h",
        "ecc_p384.h",
        "ed25519.h",
        "hkdf.h",
        "hmac.h",
        "kdf_ctr.h",
        "key_transport.h",
        "kmac.h",
        "kmac_kdf.h",
        "otcrypto.h",
        "rsa.h",
        "sha2.h",
        "sha3.h",
        "x25519.h",
    ],
    defines = ["OTCRYPTO_IN_REPO=1"],
    includes = ["."],
    deps = [
        "//sw/device/lib/base:hardened",
        "//sw/device/lib/base:status",
    ],
)

# Create a library that makes the headers available as though we've been
# exported from the repo (ie: OTCRYPTO_IN_REPO is not set).
cc_library(
    name = "exported_headers_for_test",
    hdrs = [
        "aes.h",
        "aes_gcm.h",
        "datatypes.h",
        "drbg.h",
        "ecc_p256.h",
        "ecc_p384.h",
        "ed25519.h",
        "hkdf.h",
        "hmac.h",
        "kdf_ctr.h",
        "key_transport.h",
        "kmac.h",
        "kmac_kdf.h",
        "otcrypto.h",
        "rsa.h",
        "sha2.h",
        "sha3.h",
        "x25519.h",
        "//sw/device/lib/crypto/include/freestanding:absl_status.h",
        "//sw/device/lib/crypto/include/freestanding:defs.h",
        "//sw/device/lib/crypto/include/freestanding:hardened.h",
    ],
    includes = ["."],
)

pkg_files(
    name = "package",
    srcs = glob(["*.h"]),
    prefix = "crypto/include",
)
