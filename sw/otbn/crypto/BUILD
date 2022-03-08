# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:otbn.bzl", "otbn_binary", "otbn_library")

package(default_visibility = ["//visibility:public"])

otbn_binary(
    name = "p256_ecdsa",
    srcs = [
        "p256_ecdsa.s",
        "p256.s",
    ],
)

otbn_library(
    name = "rsa_verify_3072",
    srcs = [
        "//sw/vendor:veri-titan/gen/rsa_verify_3072.s",
    ],
)

otbn_library(
    name = "rsa_verify_3072_m0inv",
    srcs = [
        "rsa_verify_3072_m0inv.s",
    ],
)

otbn_library(
    name = "rsa_verify_3072_rr",
    srcs = [
        "rsa_verify_3072_rr.s",
    ],
)

otbn_binary(
    name = "run_rsa_verify_3072",
    srcs = [
        "run_rsa_verify_3072.s",
    ],
    deps = [
        ":rsa_verify_3072_rr",
        ":rsa_verify_3072_m0inv",
        ":rsa_verify_3072"
    ],
)

otbn_binary(
    name = "run_rsa_verify_3072_rr_modexp",
    srcs = [
        "run_rsa_verify_3072_rr_modexp.s",
    ],
    deps = [
        ":rsa_verify_3072_rr",
        ":rsa_verify_3072"
    ],
)
