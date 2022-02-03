# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

package(default_visibility = ["//visibility:public"])

load("//rules:opentitan.bzl", "opentitan_functest", "OPENTITAN_CPU")

opentitan_functest(
    name = "ecdsa_p256_functest",
    srcs = ["ecdsa_p256_functest.c"],
    deps = [
        "//sw/device/lib/crypto:otbn_util",
        "//sw/device/lib/crypto/drivers:hmac",
        "//sw/device/lib/crypto/drivers:otbn",
        "//sw/device/lib/crypto/ecdsa_p256",
        "//sw/device/lib/testing:entropy_testutils",
        "//sw/device/lib/runtime:log",
    ],
)

cc_library(
    name = "ecdsa_p256_verify_testvectors",
    hdrs = ["ecdsa_p256_verify_testvectors.h"],
)

opentitan_functest(
    name = "ecdsa_p256_verify_functest",
    srcs = ["ecdsa_p256_verify_functest.c"],
    deps = [
        ":ecdsa_p256_verify_testvectors",
        "//sw/device/lib/crypto:otbn_util",
        "//sw/device/lib/crypto/drivers:hmac",
        "//sw/device/lib/crypto/drivers:otbn",
        "//sw/device/lib/crypto/ecdsa_p256",
        "//sw/device/lib/runtime:log",
    ],
)
