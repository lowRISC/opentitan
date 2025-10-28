# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

package(default_visibility = ["//visibility:public"])

load("//rules/opentitan:defs.bzl", "OPENTITAN_CPU")

cc_library(
    name = "rsa_datatypes",
    hdrs = ["rsa_datatypes.h"],
)

cc_library(
    name = "rsa_encryption",
    srcs = ["rsa_encryption.c"],
    hdrs = ["rsa_encryption.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        ":rsa_datatypes",
        ":rsa_padding",
        ":run_rsa",
        "//sw/device/lib/base:hardened",
        "//sw/device/lib/base:hardened_memory",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/crypto/drivers:rv_core_ibex",
    ],
)

cc_library(
    name = "run_rsa_key_from_cofactor",
    srcs = ["run_rsa_key_from_cofactor.c"],
    hdrs = ["run_rsa_key_from_cofactor.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        ":rsa_datatypes",
        "//sw/device/lib/base:hardened",
        "//sw/device/lib/base:hardened_memory",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/crypto/drivers:otbn",
        "//sw/device/lib/crypto/drivers:rv_core_ibex",
        "//sw/otbn/crypto:run_rsa_key_from_cofactor",
    ],
)

cc_library(
    name = "run_rsa",
    srcs = ["run_rsa.c"],
    hdrs = ["run_rsa.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        ":rsa_datatypes",
        "//sw/device/lib/base:hardened_memory",
        "//sw/device/lib/crypto/drivers:otbn",
        "//sw/device/lib/runtime:log",
        "//sw/otbn/crypto:run_rsa",
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
        "//sw/device/lib/base:random_order",
        "//sw/device/lib/crypto/drivers:entropy",
        "//sw/device/lib/crypto/drivers:hmac",
        "//sw/device/lib/crypto/drivers:kmac",
        "//sw/device/lib/crypto/drivers:rv_core_ibex",
        "//sw/device/lib/crypto/impl:status",
    ],
)

cc_library(
    name = "rsa_signature",
    srcs = ["rsa_signature.c"],
    hdrs = ["rsa_signature.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        ":rsa_datatypes",
        ":rsa_padding",
        ":run_rsa",
        "//sw/device/lib/base:hardened",
        "//sw/device/lib/base:hardened_memory",
        "//sw/device/lib/base:math",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/crypto/drivers:entropy",
        "//sw/device/lib/crypto/drivers:rv_core_ibex",
    ],
)
