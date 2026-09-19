# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

package(default_visibility = ["//visibility:public"])

load("//rules/opentitan:defs.bzl", "OPENTITAN_CPU")

cc_library(
    name = "sha256",
    srcs = ["sha256.c"],
    hdrs = ["sha256.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        "//sw/device/lib/base:hardened",
        "//sw/device/lib/base:hardened_memory",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/crypto/drivers:otbn",
        "//sw/device/lib/crypto/drivers:rv_core_ibex",
        "//sw/otbn/crypto/sha2:run_sha256",
    ],
)

cc_library(
    name = "sha384",
    srcs = ["sha384.c"],
    hdrs = ["sha384.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        "//sw/device/lib/base:hardened",
        "//sw/device/lib/base:hardened_memory",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/crypto/drivers:otbn",
        "//sw/device/lib/crypto/drivers:rv_core_ibex",
        "//sw/otbn/crypto/sha2:run_sha384",
    ],
)

cc_library(
    name = "sha512",
    srcs = ["sha512.c"],
    hdrs = ["sha512.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        ":sha384",
        "//sw/device/lib/base:hardened",
        "//sw/device/lib/base:hardened_memory",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/crypto/drivers:otbn",
        "//sw/device/lib/crypto/drivers:rv_core_ibex",
        "//sw/otbn/crypto/sha2:run_sha512",
    ],
)

cc_library(
    name = "hkdf",
    srcs = ["hkdf.c"],
    hdrs = ["hkdf.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        ":sha256",
        ":sha384",
        ":sha512",
        "//sw/device/lib/base:hardened",
        "//sw/device/lib/base:hardened_memory",
        "//sw/device/lib/base:math",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/crypto/drivers:otbn",
        "//sw/device/lib/crypto/drivers:rv_core_ibex",
        "//sw/device/lib/crypto/impl:config",
        "//sw/device/lib/crypto/impl:cryptolib_build_info",
        "//sw/device/lib/crypto/impl:integrity",
        "//sw/device/lib/crypto/impl:keyblob",
        "//sw/device/lib/crypto/impl:status",
        "//sw/device/lib/crypto/include:datatypes",
        "//sw/otbn/crypto/sha2:run_hkdf_sha256",
        "//sw/otbn/crypto/sha2:run_hkdf_sha384",
        "//sw/otbn/crypto/sha2:run_hkdf_sha512",
    ],
)
