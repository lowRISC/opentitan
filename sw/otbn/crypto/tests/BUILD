# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:otbn.bzl", "otbn_consttime_test", "otbn_sim_test")

package(default_visibility = ["//visibility:public"])

otbn_sim_test(
    name = "ed25519_ext_add_test",
    srcs = [
        "ed25519_ext_add_test.s",
    ],
    exp = "ed25519_ext_add_test.exp",
    deps = [
        "//sw/otbn/crypto:ed25519",
        "//sw/otbn/crypto:field25519",
    ],
)

otbn_consttime_test(
    name = "ed25519_ext_add_consttime",
    subroutine = "ext_add",
    deps = [
        ":ed25519_ext_add_test",
    ],
)

otbn_sim_test(
    name = "ed25519_scalar_test",
    srcs = [
        "ed25519_scalar_test.s",
    ],
    exp = "ed25519_scalar_test.exp",
    deps = [
        "//sw/otbn/crypto:ed25519_scalar",
    ],
)

otbn_sim_test(
    name = "field25519_test",
    srcs = [
        "field25519_test.s",
    ],
    exp = "field25519_test.exp",
    deps = [
        "//sw/otbn/crypto:field25519",
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

otbn_sim_test(
    name = "p256_base_mult_test",
    srcs = [
        "p256_base_mult_test.s",
    ],
    exp = "p256_base_mult_test.exp",
    deps = [
        "//sw/otbn/crypto:p256",
    ],
)

otbn_consttime_test(
    name = "p256_base_mult_consttime",
    subroutine = "p256_base_mult",
    deps = [
        "//sw/otbn/crypto:p256_ecdsa",
    ],
)

otbn_consttime_test(
    name = "p256_isoncurve_consttime",
    subroutine = "p256_isoncurve",
    deps = [
        "//sw/otbn/crypto:p256_ecdsa",
    ],
)

otbn_consttime_test(
    name = "p256_proj_add_consttime",
    subroutine = "proj_add",
    deps = [
        "//sw/otbn/crypto:p256_ecdsa",
    ],
)

otbn_consttime_test(
    name = "p256_scalar_mult_consttime",
    subroutine = "p256_scalar_mult",
    deps = [
        "//sw/otbn/crypto:p256_ecdsa",
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
#       "//sw/otbn/crypto:p256_ecdsa"
#   ],
#   subroutine = "p256_sign",
# )

otbn_sim_test(
    name = "p256_ecdsa_sign_test",
    srcs = [
        "p256_ecdsa_sign_test.s",
    ],
    exp = "p256_ecdsa_sign_test.exp",
    deps = [
        "//sw/otbn/crypto:p256",
    ],
)

otbn_sim_test(
    name = "p256_ecdsa_verify_test",
    srcs = [
        "p256_ecdsa_verify_test.s",
    ],
    exp = "p256_ecdsa_verify_test.exp",
    deps = [
        "//sw/otbn/crypto:p256",
    ],
)

otbn_sim_test(
    name = "p256_isoncurve_test",
    srcs = [
        "p256_isoncurve_test.s",
    ],
    exp = "p256_isoncurve_test.exp",
    deps = [
        "//sw/otbn/crypto:p256",
    ],
)

otbn_sim_test(
    name = "p256_proj_add_test",
    srcs = [
        "p256_proj_add_test.s",
    ],
    exp = "p256_proj_add_test.exp",
    deps = [
        "//sw/otbn/crypto:p256",
    ],
)

otbn_sim_test(
    name = "p256_scalar_mult_test",
    srcs = [
        "p256_scalar_mult_test.s",
    ],
    exp = "p256_scalar_mult_test.exp",
    deps = [
        "//sw/otbn/crypto:p256",
    ],
)

otbn_sim_test(
    name = "p384_base_mult_test",
    srcs = [
        "p384_base_mult_test.s",
    ],
    exp = "p384_base_mult_test.exp",
    deps = [
        "//sw/otbn/crypto:p384_base",
        "//sw/otbn/crypto:p384_sign",
    ],
)

otbn_sim_test(
    name = "p384_ecdsa_sign_test",
    srcs = [
        "p384_ecdsa_sign_test.s",
    ],
    exp = "p384_ecdsa_sign_test.exp",
    deps = [
        "//sw/otbn/crypto:p384_base",
        "//sw/otbn/crypto:p384_sign",
    ],
)

otbn_sim_test(
    name = "p384_ecdsa_verify_test",
    srcs = [
        "p384_ecdsa_verify_test.s",
    ],
    exp = "p384_ecdsa_verify_test.exp",
    deps = [
        "//sw/otbn/crypto:p384_base",
        "//sw/otbn/crypto:p384_verify",
    ],
)

otbn_sim_test(
    name = "p384_isoncurve_test",
    srcs = [
        "p384_isoncurve_test.s",
    ],
    exp = "p384_isoncurve_test.exp",
    deps = [
        "//sw/otbn/crypto:p384_base",
        "//sw/otbn/crypto:p384_verify",
    ],
)

otbn_sim_test(
    name = "p384_proj_add_test",
    srcs = [
        "p384_proj_add_test.s",
    ],
    exp = "p384_proj_add_test.exp",
    deps = [
        "//sw/otbn/crypto:p384_base",
    ],
)

otbn_sim_test(
    name = "p384_scalar_mult_test",
    srcs = [
        "p384_scalar_mult_test.s",
    ],
    exp = "p384_scalar_mult_test.exp",
    deps = [
        "//sw/otbn/crypto:p384_base",
        "//sw/otbn/crypto:p384_sign",
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

otbn_sim_test(
    name = "rsa_1024_dec_test",
    srcs = [
        "rsa_1024_dec_test.s",
    ],
    exp = "rsa_1024_dec_test.exp",
    deps = [
        "//sw/otbn/crypto:modexp",
    ],
)

otbn_sim_test(
    name = "rsa_1024_enc_test",
    srcs = [
        "rsa_1024_enc_test.s",
    ],
    exp = "rsa_1024_enc_test.exp",
    deps = [
        "//sw/otbn/crypto:modexp",
    ],
)

otbn_sim_test(
    name = "rsa_verify_test",
    srcs = [
        "rsa_verify_test.s",
    ],
    exp = "rsa_verify_test.exp",
    deps = [
        "//sw/otbn/crypto:rsa_verify",
    ],
)

otbn_sim_test(
    name = "rsa_verify_exp3_test",
    srcs = [
        "rsa_verify_exp3_test.s",
    ],
    exp = "rsa_verify_exp3_test.exp",
    deps = [
        "//sw/otbn/crypto:rsa_verify",
    ],
)

otbn_sim_test(
    name = "rsa_verify_3072_consts_test",
    srcs = [
        "rsa_verify_3072_consts_test.s",
    ],
    exp = "rsa_verify_3072_consts_test.exp",
    deps = [
        "//sw/otbn/crypto:rsa_verify_3072",
        "//sw/otbn/crypto:rsa_verify_3072_m0inv",
        "//sw/otbn/crypto:rsa_verify_3072_rr",
    ],
)

otbn_sim_test(
    name = "rsa_verify_3072_test",
    srcs = [
        "rsa_verify_3072_test.s",
    ],
    exp = "rsa_verify_3072_test.exp",
    deps = [
        "//sw/otbn/crypto:rsa_verify_3072",
    ],
)

otbn_sim_test(
    name = "sha512_test",
    srcs = [
        "sha512_test.s",
    ],
    exp = "sha512_test.exp",
    deps = [
        "//sw/otbn/crypto:sha512",
    ],
)

otbn_sim_test(
    name = "x25519_test",
    srcs = [
        "x25519_test.s",
    ],
    exp = "x25519_test.exp",
    deps = [
        "//sw/otbn/crypto:field25519",
        "//sw/otbn/crypto:x25519",
    ],
)

otbn_consttime_test(
    name = "x25519_consttime",
    subroutine = "X25519",
    deps = [
        ":x25519_test",
    ],
)
