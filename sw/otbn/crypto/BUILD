# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:otbn.bzl", "otbn_binary", "otbn_library")

package(default_visibility = ["//visibility:public"])

otbn_binary(
    name = "boot",
    srcs = [
        "boot.s",
    ],
    deps = [
        ":p256_base",
        ":p256_isoncurve",
        ":p256_sign",
        ":p256_verify",
    ],
)

otbn_library(
    name = "ed25519",
    srcs = [
        "ed25519.s",
    ],
)

otbn_sim_test(
    name = "ed25519_encode_decode_test",
    srcs = [
        "ed25519_encode_decode_test.s",
    ],
    deps = [
        ":ed25519",
        ":ed25519_scalar",
        ":field25519",
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
    name = "p256_shared_key",
    srcs = [
        "p256_shared_key.s",
    ],
)

otbn_library(
    name = "p256_base",
    srcs = [
        "p256_base.s",
    ],
)

otbn_library(
    name = "p256_isoncurve",
    srcs = [
        "p256_isoncurve.s",
    ],
)

otbn_library(
    name = "p256_isoncurve_proj",
    srcs = [
        "p256_isoncurve_proj.s",
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
    name = "run_p256",
    srcs = [
        "run_p256.s",
    ],
    deps = [
        ":p256_base",
        ":p256_isoncurve",
        ":p256_isoncurve_proj",
        ":p256_shared_key",
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
    name = "p384_b2a",
    srcs = [
        "p384_b2a.s",
    ],
)

otbn_library(
    name = "p384_isoncurve",
    srcs = [
        "p384_isoncurve.s",
    ],
)

otbn_library(
    name = "p384_isoncurve_proj",
    srcs = [
        "p384_isoncurve_proj.s",
    ],
)

otbn_library(
    name = "p384_mem",
    srcs = [
        "p384_mem.s",
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
    name = "p384_keygen_from_seed",
    srcs = [
        "p384_keygen_from_seed.s",
    ],
)

otbn_library(
    name = "p384_base_mult",
    srcs = [
        "p384_base_mult.s",
    ],
)

otbn_library(
    name = "p384_modinv",
    srcs = [
        "p384_modinv.s",
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
    name = "rsa_primality",
    srcs = [
        "rsa_primality.s",
    ],
)

otbn_library(
    name = "run_rsa_mem",
    srcs = [
        "run_rsa_mem.s",
    ],
)

otbn_library(
    name = "rsa_keygen",
    srcs = [
        "rsa_keygen.s",
    ],
)

otbn_library(
    name = "rsa_modinv_f4",
    srcs = [
        "rsa_modinv_f4.s",
    ],
)

otbn_binary(
    name = "run_rsa",
    srcs = [
        "gcd.s",
        "modexp.s",
        "montmul.s",
        "mul.s",
        "rsa_keygen.s",
        "rsa_modinv_f4.s",
        "rsa_primality.s",
        "run_rsa.s",
        "run_rsa_mem.s",
    ],
)

otbn_library(
    name = "run_rsa_key_from_cofactor_mem",
    srcs = [
        "run_rsa_key_from_cofactor_mem.s",
    ],
)

otbn_library(
    name = "rsa_key_from_cofactor",
    srcs = [
        "rsa_key_from_cofactor.s",
    ],
)

otbn_binary(
    name = "run_rsa_key_from_cofactor",
    srcs = [
        "run_rsa_key_from_cofactor.s",
    ],
    deps = [
        ":div",
        ":gcd",
        ":lcm",
        ":montmul",
        ":mul",
        ":rsa_key_from_cofactor",
        ":rsa_modinv_f4",
        ":run_rsa_key_from_cofactor_mem",
    ],
)

otbn_binary(
    name = "p256_ecdsa_sca",
    srcs = [
        "p256_ecdsa_sca.s",
    ],
    deps = [
        ":p256_base",
        ":p256_isoncurve",
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
        ":p256_isoncurve",
    ],
)

otbn_binary(
    name = "p256_mod_inv_sca",
    srcs = [
        "p256_mod_inv_sca.s",
    ],
    deps = [
        ":p256_base",
        ":p256_isoncurve",
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
        ":p384_isoncurve",
        ":p384_mem",
        ":p384_modinv",
        ":p384_sign",
    ],
)

otbn_binary(
    name = "run_p384",
    srcs = [
        "run_p384.s",
    ],
    deps = [
        ":p384_a2b",
        ":p384_b2a",
        ":p384_base",
        ":p384_base_mult",
        ":p384_internal_mult",
        ":p384_isoncurve",
        ":p384_isoncurve_proj",
        ":p384_keygen",
        ":p384_keygen_from_seed",
        ":p384_mem",
        ":p384_modinv",
        ":p384_scalar_mult",
        ":p384_sign",
        ":p384_verify",
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
    name = "sha3_shake",
    srcs = [
        "sha3_shake.s",
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
