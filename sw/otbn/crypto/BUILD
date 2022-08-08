# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:otbn.bzl", "otbn_binary", "otbn_consttime_test", "otbn_library", "otbn_sim_test")

package(default_visibility = ["//visibility:public"])

otbn_library(
    name = "ed25519",
    srcs = [
        "ed25519.s",
    ],
)

otbn_sim_test(
    name = "ed25519_ext_add_test",
    srcs = [
        "ed25519_ext_add_test.s",
    ],
    deps = [
        ":ed25519",
        ":field25519",
    ],
)

otbn_consttime_test(
    name = "ed25519_ext_add_consttime",
    subroutine = "ext_add",
    deps = [
        ":ed25519_ext_add_test",
    ],
)

otbn_library(
    name = "ed25519_scalar",
    srcs = [
        "ed25519_scalar.s",
    ],
)

otbn_sim_test(
    name = "ed25519_scalar_test",
    srcs = [
        "ed25519_scalar_test.s",
    ],
    deps = [
        ":ed25519_scalar",
    ],
)

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

otbn_consttime_test(
    name = "field25519_fe_inv_consttime",
    subroutine = "fe_inv",
    deps = [
        ":field25519_test",
    ],
)

otbn_consttime_test(
    name = "field25519_fe_mul_consttime",
    subroutine = "fe_mul",
    deps = [
        ":field25519_test",
    ],
)

otbn_consttime_test(
    name = "field25519_fe_square_consttime",
    subroutine = "fe_square",
    deps = [
        ":field25519_test",
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

otbn_consttime_test(
    name = "p256_base_mult_consttime",
    subroutine = "p256_base_mult",
    deps = [
        ":p256_ecdsa",
    ],
)

otbn_consttime_test(
    name = "p256_isoncurve_consttime",
    subroutine = "p256_isoncurve",
    deps = [
        ":p256_ecdsa",
    ],
)

otbn_consttime_test(
    name = "p256_proj_add_consttime",
    subroutine = "proj_add",
    deps = [
        ":p256_ecdsa",
    ],
)

otbn_consttime_test(
    name = "p256_scalar_mult_consttime",
    subroutine = "p256_scalar_mult",
    deps = [
        ":p256_ecdsa",
    ],
)

# TODO: Add more fine-grained DMEM tracing to the constant-time checker. This
# test fails because p256_sign branches based on some non-secret values from
# DMEM. However, since there are also secret values in DMEM, it's not safe to
# mark DMEM non-secret, and the constant-time checker doesn't currently have
# the ability to track different DMEM regions separately.
#
# otbn_consttime_test(
#   name = "p256_sign_consttime",
#   deps = [
#       ":p256_ecdsa"
#   ],
#   subroutine = "p256_sign",
# )

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

otbn_consttime_test(
    name = "p384_base_mult_consttime",
    subroutine = "p384_base_mult",
    deps = [
        ":p384_ecdsa_sign_test",
    ],
)

otbn_consttime_test(
    name = "p384_mulmod_p_consttime",
    subroutine = "p384_mulmod_p",
    deps = [
        ":p384_ecdsa_sign_test",
    ],
)

otbn_consttime_test(
    name = "p384_mulmod_n_consttime",
    subroutine = "p384_mulmod_n",
    deps = [
        ":p384_ecdsa_sign_test",
    ],
)

# TODO: Add more fine-grained DMEM tracing to the constant-time checker. This
# test fails because p384_sign branches based on some non-secret values from
# DMEM. However, since there are also secret values in DMEM, it's not safe to
# mark DMEM non-secret, and the constant-time checker doesn't currently have
# the ability to track different DMEM regions separately.
#
# otbn_consttime_test(
#   name = "p384_sign_consttime",
#   deps = [
#       ":p384_ecdsa_sign_test"
#   ],
#   subroutine = "p384_sign",
# )

otbn_consttime_test(
    name = "proj_add_p384_consttime",
    initial_constants = [
        "x22:10",
        "x23:11",
        "x24:16",
        "x25:17",
    ],
    subroutine = "proj_add_p384",
    deps = [
        ":p384_ecdsa_sign_test",
    ],
)

otbn_consttime_test(
    name = "scalar_mult_p384_consttime",
    subroutine = "scalar_mult_p384",
    deps = [
        ":p384_ecdsa_sign_test",
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
        "//sw/vendor:veri-titan/gen/otbn_modexp.s",
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

otbn_binary(
    name = "p256_ecdsa_sca",
    srcs = [
        "p256_ecdsa_sca.s",
    ],
    deps = [
        ":p256",
    ],
)

otbn_binary(
    name = "p384_ecdsa_sca",
    srcs = [
        "p384_ecdsa_sca.s",
    ],
    deps = [
        ":p384_base",
        ":p384_sign",
    ],
)

otbn_library(
    name = "x25519",
    srcs = [
        "x25519.s",
    ],
)

otbn_binary(
    name = "x25519_sideload",
    srcs = [
        "x25519_sideload.s",
    ],
    deps = [
        ":field25519",
        ":x25519",
    ],
)

otbn_sim_test(
    name = "x25519_test",
    srcs = [
        "x25519_test.s",
    ],
    deps = [
        ":field25519",
        ":x25519",
    ],
)

otbn_consttime_test(
    name = "x25519_consttime",
    subroutine = "X25519",
    deps = [
        ":x25519_test",
    ],
)
