# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:otbn.bzl", "otbn_binary", "otbn_library", "otbn_sim_test")

package(default_visibility = ["//visibility:public"])

otbn_library(
    name = "field25519",
    srcs = [
        "field25519.s",
    ],
)

otbn_sim_test(
    name = "field25519_test",
    srcs = [
        "field25519_test.s",
    ],
    deps = [
        ":field25519",
    ],
)

otbn_library(
    name = "modexp",
    srcs = [
        "modexp.s",
    ],
)

otbn_library(
    name = "p256",
    srcs = [
        "p256.s",
    ],
)

otbn_binary(
    name = "p256_base_mult_test",
    srcs = [
        "p256_base_mult_test.s",
    ],
    deps = [
        ":p256",
    ],
)

otbn_binary(
    name = "p256_ecdsa",
    srcs = [
        "p256_ecdsa.s",
    ],
    deps = [
        ":p256",
    ],
)

otbn_binary(
    name = "p256_ecdsa_sign_test",
    srcs = [
        "p256_ecdsa_sign_test.s",
    ],
    deps = [
        ":p256",
    ],
)

otbn_binary(
    name = "p256_ecdsa_verify_test",
    srcs = [
        "p256_ecdsa_verify_test.s",
    ],
    deps = [
        ":p256",
    ],
)

otbn_binary(
    name = "p256_isoncurve_test",
    srcs = [
        "p256_isoncurve_test.s",
    ],
    deps = [
        ":p256",
    ],
)

otbn_binary(
    name = "p256_proj_add_test",
    srcs = [
        "p256_proj_add_test.s",
    ],
    deps = [
        ":p256",
    ],
)

otbn_binary(
    name = "p256_scalar_mult_test",
    srcs = [
        "p256_scalar_mult_test.s",
    ],
    deps = [
        ":p256",
    ],
)

otbn_library(
    name = "p384_base",
    srcs = [
        "p384_base.s",
    ],
)

otbn_library(
    name = "p384_sign",
    srcs = [
        "p384_sign.s",
    ],
)

otbn_library(
    name = "p384_verify",
    srcs = [
        "p384_verify.s",
    ],
)

otbn_binary(
    name = "p384_base_mult_test",
    srcs = [
        "p384_base_mult_test.s",
    ],
    deps = [
        ":p384_base",
        ":p384_sign",
    ],
)

otbn_binary(
    name = "p384_ecdsa_sign_test",
    srcs = [
        "p384_ecdsa_sign_test.s",
    ],
    deps = [
        ":p384_base",
        ":p384_sign",
    ],
)

otbn_binary(
    name = "p384_ecdsa_verify_test",
    srcs = [
        "p384_ecdsa_verify_test.s",
    ],
    deps = [
        ":p384_base",
        ":p384_verify",
    ],
)

otbn_binary(
    name = "p384_isoncurve_test",
    srcs = [
        "p384_isoncurve_test.s",
    ],
    deps = [
        ":p384_base",
        ":p384_verify",
    ],
)

otbn_binary(
    name = "p384_proj_add_test",
    srcs = [
        "p384_proj_add_test.s",
    ],
    deps = [
        ":p384_base",
    ],
)

otbn_binary(
    name = "p384_scalar_mult_test",
    srcs = [
        "p384_scalar_mult_test.s",
    ],
    deps = [
        ":p384_base",
        ":p384_sign",
    ],
)

otbn_binary(
    name = "rsa",
    srcs = [
        "rsa.s",
    ],
    deps = [
        ":modexp",
    ],
)

otbn_binary(
    name = "rsa_1024_dec_test",
    srcs = [
        "rsa_1024_dec_test.s",
    ],
    deps = [
        ":modexp",
    ],
)

otbn_binary(
    name = "rsa_1024_enc_test",
    srcs = [
        "rsa_1024_enc_test.s",
    ],
    deps = [
        ":modexp",
    ],
)

otbn_library(
    name = "rsa_verify",
    srcs = [
        "rsa_verify.s",
    ],
)

otbn_binary(
    name = "rsa_verify_test",
    srcs = [
        "rsa_verify_test.s",
    ],
    deps = [
        ":rsa_verify",
    ],
)

otbn_binary(
    name = "rsa_verify_test_exp3",
    srcs = [
        "rsa_verify_test_exp3.s",
    ],
    deps = [
        ":rsa_verify",
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
    name = "rsa_verify_3072_consts_test",
    srcs = [
        "rsa_verify_3072_consts_test.s",
    ],
    deps = [
        ":rsa_verify_3072",
        ":rsa_verify_3072_m0inv",
        ":rsa_verify_3072_rr",
    ],
)

otbn_binary(
    name = "rsa_verify_3072_test",
    srcs = [
        "rsa_verify_3072_test.s",
    ],
    deps = [
        ":rsa_verify_3072",
    ],
)

otbn_binary(
    name = "run_rsa_verify_3072",
    srcs = [
        "run_rsa_verify_3072.s",
    ],
    deps = [
        ":rsa_verify_3072",
        ":rsa_verify_3072_m0inv",
        ":rsa_verify_3072_rr",
    ],
)

otbn_binary(
    name = "run_rsa_verify_3072_rr_modexp",
    srcs = [
        "run_rsa_verify_3072_rr_modexp.s",
    ],
    deps = [
        ":rsa_verify_3072",
        ":rsa_verify_3072_rr",
    ],
)
