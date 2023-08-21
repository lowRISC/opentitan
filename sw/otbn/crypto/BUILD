# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:otbn.bzl", "otbn_binary", "otbn_library")

package(default_visibility = ["//visibility:public"])

otbn_library(
    name = "ed25519",
    srcs = [
        "ed25519.s",
    ],
)

otbn_library(
    name = "ed25519_scalar",
    srcs = [
        "ed25519_scalar.s",
    ],
)

otbn_library(
    name = "div",
    srcs = [
        "div.s",
    ],
)

otbn_library(
    name = "field25519",
    srcs = [
        "field25519.s",
    ],
)

otbn_library(
    name = "gcd",
    srcs = [
        "gcd.s",
    ],
)

otbn_library(
    name = "lcm",
    srcs = [
        "lcm.s",
    ],
)

otbn_library(
    name = "modexp",
    srcs = [
        "modexp.s",
    ],
)

otbn_library(
    name = "montmul",
    srcs = [
        "montmul.s",
    ],
)

otbn_library(
    name = "mul",
    srcs = [
        "mul.s",
    ],
)

otbn_library(
    name = "p256_a2b",
    srcs = [
        "p256_a2b.s",
    ],
)

otbn_library(
    name = "p256_base",
    srcs = [
        "p256_base.s",
    ],
)

otbn_library(
    name = "p256_sign",
    srcs = [
        "p256_sign.s",
    ],
)

otbn_library(
    name = "p256_verify",
    srcs = [
        "p256_verify.s",
    ],
)

otbn_binary(
    name = "p256_ecdh",
    srcs = [
        "p256_ecdh.s",
    ],
    deps = [
        ":p256_a2b",
        ":p256_base",
    ],
)

otbn_binary(
    name = "p256_ecdsa",
    srcs = [
        "p256_ecdsa.s",
    ],
    deps = [
        ":p256_base",
        ":p256_sign",
        ":p256_verify",
    ],
)

otbn_library(
    name = "p384_base",
    srcs = [
        "p384_base.s",
    ],
)

otbn_library(
    name = "p384_a2b",
    srcs = [
        "p384_a2b.s",
    ],
)

otbn_library(
    name = "p384_sign",
    srcs = [
        "p384_sign.s",
    ],
)

otbn_library(
    name = "p384_internal_mult",
    srcs = [
        "p384_internal_mult.s",
    ],
)

otbn_library(
    name = "p384_keygen",
    srcs = [
        "p384_keygen.s",
    ],
)

otbn_library(
    name = "p384_scalar_mult",
    srcs = [
        "p384_scalar_mult.s",
    ],
)

otbn_library(
    name = "p384_verify",
    srcs = [
        "p384_verify.s",
    ],
)

otbn_library(
    name = "primality",
    srcs = [
        "primality.s",
    ],
)

otbn_binary(
    name = "rsa",
    srcs = [
        "rsa.s",
    ],
    deps = [
        ":modexp",
        ":montmul",
    ],
)

otbn_binary(
    name = "run_rsa_modexp",
    srcs = [
        "run_rsa_modexp.s",
    ],
    deps = [
        ":modexp",
        ":montmul",
    ],
)

otbn_library(
    name = "rsa_keygen",
    srcs = [
        "rsa_keygen.s",
    ],
)

otbn_binary(
    name = "run_rsa_keygen",
    srcs = [
        "run_rsa_keygen.s",
    ],
    deps = [
        ":div",
        ":gcd",
        ":lcm",
        ":montmul",
        ":mul",
        ":primality",
        ":rsa_keygen",
    ],
)

otbn_library(
    name = "rsa_verify",
    srcs = [
        "rsa_verify.s",
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
        ":p256_base",
        ":p256_sign",
        ":p256_verify",
    ],
)

otbn_binary(
    name = "p256_key_from_seed_sca",
    srcs = [
        "p256_key_from_seed_sca.s",
    ],
    deps = [
        ":p256_base",
    ],
)

otbn_binary(
    name = "p256_mod_inv_sca",
    srcs = [
        "p256_mod_inv_sca.s",
    ],
    deps = [
        ":p256_base",
    ],
)

otbn_binary(
    name = "p384_ecdsa_sca",
    srcs = [
        "p384_ecdsa_sca.s",
    ],
    deps = [
        ":p384_base",
        ":p384_internal_mult",
        ":p384_sign",
    ],
)

otbn_library(
    name = "sha256",
    srcs = [
        "sha256.s",
    ],
)

otbn_binary(
    name = "run_sha256",
    srcs = [
        "run_sha256.s",
    ],
    deps = [
        ":sha256",
    ],
)

otbn_library(
    name = "sha512",
    srcs = [
        "sha512.s",
    ],
)

otbn_binary(
    name = "run_sha512",
    srcs = [
        "run_sha512.s",
    ],
    deps = [
        ":sha512",
    ],
)

otbn_library(
    name = "sha512_compact",
    srcs = [
        "sha512_compact.s",
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
