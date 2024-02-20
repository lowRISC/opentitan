# Copyright lowRISC contributors.
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
        "datatypes.h",
        "drbg.h",
        "ecc.h",
        "hash.h",
        "kdf.h",
        "key_transport.h",
        "mac.h",
        "rsa.h",
    ],
    defines = ["OTCRYPTO_IN_REPO=1"],
    includes = ["."],
    deps = [
        "//sw/device/lib/base:hardened",
        "//sw/device/lib/base:status",
    ],
)

pkg_files(
    name = "package",
    srcs = glob(["*.h"]),
    prefix = "crypto/include",
)
