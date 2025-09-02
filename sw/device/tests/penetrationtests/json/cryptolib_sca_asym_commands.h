// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_JSON_CRYPTOLIB_SCA_ASYM_COMMANDS_H_
#define OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_JSON_CRYPTOLIB_SCA_ASYM_COMMANDS_H_
#include "sw/device/lib/ujson/ujson_derive.h"
#ifdef __cplusplus
extern "C" {
#endif

#define MODULE_ID MAKE_MODULE_ID('j', 's', 'a')

#define RSA_CMD_MAX_MESSAGE_BYTES 512
#define RSA_CMD_MAX_N_BYTES 512
#define RSA_CMD_MAX_SIGNATURE_BYTES 512

#define P256_CMD_BYTES 32
#define P384_CMD_BYTES 48
#define SECP256K1_CMD_BYTES 32
#define X25519_CMD_BYTES 32
#define ED25519_CMD_SCALAR_BYTES 32
#define ED25519_CMD_MAX_MSG_BYTES 128
#define ED25519_CMD_SIG_BYTES 64

// clang-format off

#define CRYPTOLIBSCAASYM_SUBCOMMAND(_, value) \
    value(_, RsaDec) \
    value(_, RsaSign) \
    value(_, Prime) \
    value(_, P256BaseMulFvsr) \
    value(_, P256BaseMulDaisy) \
    value(_, P256PointMul) \
    value(_, P256Ecdh) \
    value(_, P256Sign) \
    value(_, P384BaseMulFvsr) \
    value(_, P384BaseMulDaisy) \
    value(_, P384PointMul) \
    value(_, P384Ecdh) \
    value(_, P384Sign) \
    value(_, Secp256k1BaseMulFvsr) \
    value(_, Secp256k1BaseMulDaisy) \
    value(_, Secp256k1PointMul) \
    value(_, Secp256k1Ecdh) \
    value(_, Secp256k1Sign) \
    value(_, X25519BaseMulFvsr) \
    value(_, X25519BaseMulDaisy) \
    value(_, X25519PointMul) \
    value(_, X25519Ecdh) \
    value(_, Ed25519BaseMulFvsr) \
    value(_, Ed25519BaseMulDaisy) \
    value(_, Ed25519Sign) \
    value(_, Init)
C_ONLY(UJSON_SERDE_ENUM(CryptoLibScaAsymSubcommand, cryptolib_sca_asym_subcommand_t, CRYPTOLIBSCAASYM_SUBCOMMAND));
RUST_ONLY(UJSON_SERDE_ENUM(CryptoLibScaAsymSubcommand, cryptolib_sca_asym_subcommand_t, CRYPTOLIBSCAASYM_SUBCOMMAND, RUST_DEFAULT_DERIVE, strum::EnumString));

#define CRYPTOLIBSCAASYM_RSA_DEC_IN(field, string) \
    field(data, uint8_t, RSA_CMD_MAX_MESSAGE_BYTES) \
    field(data_len, size_t) \
    field(mode, size_t) \
    field(e, uint32_t) \
    field(n, uint8_t, RSA_CMD_MAX_N_BYTES) \
    field(d, uint8_t, RSA_CMD_MAX_N_BYTES) \
    field(n_len, size_t) \
    field(hashing, size_t) \
    field(padding, size_t) \
    field(cfg, size_t) \
    field(trigger, size_t)
UJSON_SERDE_STRUCT(CryptoLibScaAsymRsaDecIn, cryptolib_sca_asym_rsa_dec_in_t, CRYPTOLIBSCAASYM_RSA_DEC_IN);

#define CRYPTOLIBSCAASYM_RSA_DEC_OUT(field, string) \
    field(n, uint8_t, RSA_CMD_MAX_N_BYTES) \
    field(d, uint8_t, RSA_CMD_MAX_N_BYTES) \
    field(n_len, size_t) \
    field(data, uint8_t, RSA_CMD_MAX_MESSAGE_BYTES) \
    field(data_len, size_t) \
    field(status, size_t) \
    field(cfg, size_t)
UJSON_SERDE_STRUCT(CryptoLibScaAsymRsaDecOut, cryptolib_sca_asym_rsa_dec_out_t, CRYPTOLIBSCAASYM_RSA_DEC_OUT);

#define CRYPTOLIBSCAASYM_RSA_SIGN_IN(field, string) \
    field(data, uint8_t, RSA_CMD_MAX_MESSAGE_BYTES) \
    field(data_len, size_t) \
    field(e, uint32_t) \
    field(n, uint8_t, RSA_CMD_MAX_N_BYTES) \
    field(d, uint8_t, RSA_CMD_MAX_N_BYTES) \
    field(n_len, size_t) \
    field(hashing, size_t) \
    field(padding, size_t) \
    field(cfg, size_t) \
    field(num_iterations, size_t) \
    field(trigger, size_t)
UJSON_SERDE_STRUCT(CryptoLibScaAsymRsaSignIn, cryptolib_sca_asym_rsa_sign_in_t, CRYPTOLIBSCAASYM_RSA_SIGN_IN);

#define CRYPTOLIBSCAASYM_RSA_SIGN_OUT(field, string) \
    field(n, uint8_t, RSA_CMD_MAX_N_BYTES) \
    field(d, uint8_t, RSA_CMD_MAX_N_BYTES) \
    field(n_len, size_t) \
    field(sig, uint8_t, RSA_CMD_MAX_SIGNATURE_BYTES) \
    field(sig_len, size_t) \
    field(status, size_t) \
    field(cfg, size_t)
UJSON_SERDE_STRUCT(CryptoLibScaAsymRsaSignOut, cryptolib_sca_asym_rsa_sign_out_t, CRYPTOLIBSCAASYM_RSA_SIGN_OUT);

#define CRYPTOLIBSCAASYM_PRIME_IN(field, string) \
    field(e, uint32_t) \
    field(cfg, size_t) \
    field(trigger, size_t)
UJSON_SERDE_STRUCT(CryptoLibScaAsymPrimeIn, cryptolib_sca_asym_prime_in_t, CRYPTOLIBSCAASYM_PRIME_IN);

#define CRYPTOLIBSCAASYM_PRIME_OUT(field, string) \
    field(prime, uint8_t, RSA_CMD_MAX_N_BYTES) \
    field(prime_len, size_t) \
    field(status, size_t) \
    field(cfg, size_t)
UJSON_SERDE_STRUCT(CryptoLibScaAsymPrimeOut, cryptolib_sca_asym_prime_out_t, CRYPTOLIBSCAASYM_PRIME_OUT);

#define CRYPTOLIBSCAASYM_P256_BASE_MUL_IN(field, string) \
    field(scalar, uint8_t, P256_CMD_BYTES) \
    field(cfg, size_t) \
    field(num_iterations, size_t) \
    field(trigger, size_t)
UJSON_SERDE_STRUCT(CryptoLibScaAsymP256BaseMulIn, cryptolib_sca_asym_p256_base_mul_in_t, CRYPTOLIBSCAASYM_P256_BASE_MUL_IN);

#define CRYPTOLIBSCAASYM_P256_BASE_MUL_OUT(field, string) \
    field(x, uint8_t, P256_CMD_BYTES) \
    field(y, uint8_t, P256_CMD_BYTES) \
    field(status, size_t) \
    field(cfg, size_t)
UJSON_SERDE_STRUCT(CryptoLibScaAsymP256BaseMulOut, cryptolib_sca_asym_p256_base_mul_out_t, CRYPTOLIBSCAASYM_P256_BASE_MUL_OUT);

#define CRYPTOLIBSCAASYM_P256_POINT_MUL_IN(field, string) \
    field(scalar_alice, uint8_t, P256_CMD_BYTES) \
    field(scalar_bob, uint8_t, P256_CMD_BYTES) \
    field(cfg, size_t) \
    field(trigger, size_t)
UJSON_SERDE_STRUCT(CryptoLibScaAsymP256PointMulIn, cryptolib_sca_asym_p256_point_mul_in_t, CRYPTOLIBSCAASYM_P256_POINT_MUL_IN);

#define CRYPTOLIBSCAASYM_P256_POINT_MUL_OUT(field, string) \
    field(x, uint8_t, P256_CMD_BYTES) \
    field(y, uint8_t, P256_CMD_BYTES) \
    field(status, size_t) \
    field(cfg, size_t)
UJSON_SERDE_STRUCT(CryptoLibScaAsymP256PointMulOut, cryptolib_sca_asym_p256_point_mul_out_t, CRYPTOLIBSCAASYM_P256_POINT_MUL_OUT);

#define CRYPTOLIBSCAASYM_P256_ECDH_IN(field, string) \
    field(private_key, uint8_t, P256_CMD_BYTES) \
    field(public_x, uint8_t, P256_CMD_BYTES) \
    field(public_y, uint8_t, P256_CMD_BYTES) \
    field(cfg, size_t) \
    field(trigger, size_t)
UJSON_SERDE_STRUCT(CryptoLibScaAsymP256EcdhIn, cryptolib_sca_asym_p256_ecdh_in_t, CRYPTOLIBSCAASYM_P256_ECDH_IN);

#define CRYPTOLIBSCAASYM_P256_ECDH_OUT(field, string) \
    field(shared_key, uint8_t, P256_CMD_BYTES) \
    field(status, size_t) \
    field(cfg, size_t)
UJSON_SERDE_STRUCT(CryptoLibScaAsymP256EcdhOut, cryptolib_sca_asym_p256_ecdh_out_t, CRYPTOLIBSCAASYM_P256_ECDH_OUT);

#define CRYPTOLIBSCAASYM_P256_SIGN_IN(field, string) \
    field(scalar, uint8_t, P256_CMD_BYTES) \
    field(pubx, uint8_t, P256_CMD_BYTES) \
    field(puby, uint8_t, P256_CMD_BYTES) \
    field(message, uint8_t, P256_CMD_BYTES) \
    field(cfg, size_t) \
    field(trigger, size_t)
UJSON_SERDE_STRUCT(CryptoLibScaAsymP256SignIn, cryptolib_sca_asym_p256_sign_in_t, CRYPTOLIBSCAASYM_P256_SIGN_IN);

#define CRYPTOLIBSCAASYM_P256_SIGN_OUT(field, string) \
    field(r, uint8_t, P256_CMD_BYTES) \
    field(s, uint8_t, P256_CMD_BYTES) \
    field(pubx, uint8_t, P256_CMD_BYTES) \
    field(puby, uint8_t, P256_CMD_BYTES) \
    field(status, size_t) \
    field(cfg, size_t)
UJSON_SERDE_STRUCT(CryptoLibScaAsymP256SignOut, cryptolib_sca_asym_p256_sign_out_t, CRYPTOLIBSCAASYM_P256_SIGN_OUT);

#define CRYPTOLIBSCAASYM_P384_BASE_MUL_IN(field, string) \
    field(scalar, uint8_t, P384_CMD_BYTES) \
    field(cfg, size_t) \
    field(num_iterations, size_t) \
    field(trigger, size_t)
UJSON_SERDE_STRUCT(CryptoLibScaAsymP384BaseMulIn, cryptolib_sca_asym_p384_base_mul_in_t, CRYPTOLIBSCAASYM_P384_BASE_MUL_IN);

#define CRYPTOLIBSCAASYM_P384_BASE_MUL_OUT(field, string) \
    field(x, uint8_t, P384_CMD_BYTES) \
    field(y, uint8_t, P384_CMD_BYTES) \
    field(status, size_t) \
    field(cfg, size_t)
UJSON_SERDE_STRUCT(CryptoLibScaAsymP384BaseMulOut, cryptolib_sca_asym_p384_base_mul_out_t, CRYPTOLIBSCAASYM_P384_BASE_MUL_OUT);

#define CRYPTOLIBSCAASYM_P384_POINT_MUL_IN(field, string) \
    field(scalar_alice, uint8_t, P384_CMD_BYTES) \
    field(scalar_bob, uint8_t, P384_CMD_BYTES) \
    field(cfg, size_t) \
    field(trigger, size_t)
UJSON_SERDE_STRUCT(CryptoLibScaAsymP384PointMulIn, cryptolib_sca_asym_p384_point_mul_in_t, CRYPTOLIBSCAASYM_P384_POINT_MUL_IN);

#define CRYPTOLIBSCAASYM_P384_POINT_MUL_OUT(field, string) \
    field(x, uint8_t, P384_CMD_BYTES) \
    field(y, uint8_t, P384_CMD_BYTES) \
    field(status, size_t) \
    field(cfg, size_t)
UJSON_SERDE_STRUCT(CryptoLibScaAsymP384PointMulOut, cryptolib_sca_asym_p384_point_mul_out_t, CRYPTOLIBSCAASYM_P384_POINT_MUL_OUT);

#define CRYPTOLIBSCAASYM_P384_ECDH_IN(field, string) \
    field(private_key, uint8_t, P384_CMD_BYTES) \
    field(public_x, uint8_t, P384_CMD_BYTES) \
    field(public_y, uint8_t, P384_CMD_BYTES) \
    field(cfg, size_t) \
    field(trigger, size_t)
UJSON_SERDE_STRUCT(CryptoLibScaAsymP384EcdhIn, cryptolib_sca_asym_p384_ecdh_in_t, CRYPTOLIBSCAASYM_P384_ECDH_IN);

#define CRYPTOLIBSCAASYM_P384_ECDH_OUT(field, string) \
    field(shared_key, uint8_t, P384_CMD_BYTES) \
    field(status, size_t) \
    field(cfg, size_t)
UJSON_SERDE_STRUCT(CryptoLibScaAsymP384EcdhOut, cryptolib_sca_asym_p384_ecdh_out_t, CRYPTOLIBSCAASYM_P384_ECDH_OUT);

#define CRYPTOLIBSCAASYM_P384_SIGN_IN(field, string) \
    field(scalar, uint8_t, P384_CMD_BYTES) \
    field(pubx, uint8_t, P384_CMD_BYTES) \
    field(puby, uint8_t, P384_CMD_BYTES) \
    field(message, uint8_t, P384_CMD_BYTES) \
    field(cfg, size_t) \
    field(trigger, size_t)
UJSON_SERDE_STRUCT(CryptoLibScaAsymP384SignIn, cryptolib_sca_asym_p384_sign_in_t, CRYPTOLIBSCAASYM_P384_SIGN_IN);

#define CRYPTOLIBSCAASYM_P384_SIGN_OUT(field, string) \
    field(r, uint8_t, P384_CMD_BYTES) \
    field(s, uint8_t, P384_CMD_BYTES) \
    field(pubx, uint8_t, P384_CMD_BYTES) \
    field(puby, uint8_t, P384_CMD_BYTES) \
    field(status, size_t) \
    field(cfg, size_t)
UJSON_SERDE_STRUCT(CryptoLibScaAsymP384SignOut, cryptolib_sca_asym_p384_sign_out_t, CRYPTOLIBSCAASYM_P384_SIGN_OUT);

#define CRYPTOLIBSCAASYM_SECP256K1_BASE_MUL_IN(field, string) \
    field(scalar, uint8_t, SECP256K1_CMD_BYTES) \
    field(cfg, size_t) \
    field(num_iterations, size_t) \
    field(trigger, size_t)
UJSON_SERDE_STRUCT(CryptoLibScaAsymSECP256K1BaseMulIn, cryptolib_sca_asym_secp256k1_base_mul_in_t, CRYPTOLIBSCAASYM_SECP256K1_BASE_MUL_IN);

#define CRYPTOLIBSCAASYM_SECP256K1_BASE_MUL_OUT(field, string) \
    field(x, uint8_t, SECP256K1_CMD_BYTES) \
    field(y, uint8_t, SECP256K1_CMD_BYTES) \
    field(status, size_t) \
    field(cfg, size_t)
UJSON_SERDE_STRUCT(CryptoLibScaAsymSECP256K1BaseMulOut, cryptolib_sca_asym_secp256k1_base_mul_out_t, CRYPTOLIBSCAASYM_SECP256K1_BASE_MUL_OUT);

#define CRYPTOLIBSCAASYM_SECP256K1_POINT_MUL_IN(field, string) \
    field(scalar_alice, uint8_t, SECP256K1_CMD_BYTES) \
    field(scalar_bob, uint8_t, SECP256K1_CMD_BYTES) \
    field(cfg, size_t) \
    field(trigger, size_t)
UJSON_SERDE_STRUCT(CryptoLibScaAsymSECP256K1PointMulIn, cryptolib_sca_asym_secp256k1_point_mul_in_t, CRYPTOLIBSCAASYM_SECP256K1_POINT_MUL_IN);

#define CRYPTOLIBSCAASYM_SECP256K1_POINT_MUL_OUT(field, string) \
    field(x, uint8_t, SECP256K1_CMD_BYTES) \
    field(y, uint8_t, SECP256K1_CMD_BYTES) \
    field(status, size_t) \
    field(cfg, size_t)
UJSON_SERDE_STRUCT(CryptoLibScaAsymSECP256K1PointMulOut, cryptolib_sca_asym_secp256k1_point_mul_out_t, CRYPTOLIBSCAASYM_SECP256K1_POINT_MUL_OUT);

#define CRYPTOLIBSCAASYM_SECP256K1_ECDH_IN(field, string) \
    field(private_key, uint8_t, SECP256K1_CMD_BYTES) \
    field(public_x, uint8_t, SECP256K1_CMD_BYTES) \
    field(public_y, uint8_t, SECP256K1_CMD_BYTES) \
    field(cfg, size_t) \
    field(trigger, size_t)
UJSON_SERDE_STRUCT(CryptoLibScaAsymSECP256K1EcdhIn, cryptolib_sca_asym_secp256k1_ecdh_in_t, CRYPTOLIBSCAASYM_SECP256K1_ECDH_IN);

#define CRYPTOLIBSCAASYM_SECP256K1_ECDH_OUT(field, string) \
    field(shared_key, uint8_t, SECP256K1_CMD_BYTES) \
    field(status, size_t) \
    field(cfg, size_t)
UJSON_SERDE_STRUCT(CryptoLibScaAsymSECP256K1EcdhOut, cryptolib_sca_asym_secp256k1_ecdh_out_t, CRYPTOLIBSCAASYM_SECP256K1_ECDH_OUT);

#define CRYPTOLIBSCAASYM_SECP256K1_SIGN_IN(field, string) \
    field(scalar, uint8_t, SECP256K1_CMD_BYTES) \
    field(message, uint8_t, SECP256K1_CMD_BYTES) \
    field(cfg, size_t) \
    field(trigger, size_t)
UJSON_SERDE_STRUCT(CryptoLibScaAsymSECP256K1SignIn, cryptolib_sca_asym_secp256k1_sign_in_t, CRYPTOLIBSCAASYM_SECP256K1_SIGN_IN);

#define CRYPTOLIBSCAASYM_SECP256K1_SIGN_OUT(field, string) \
    field(r, uint8_t, SECP256K1_CMD_BYTES) \
    field(s, uint8_t, SECP256K1_CMD_BYTES) \
    field(pubx, uint8_t, SECP256K1_CMD_BYTES) \
    field(puby, uint8_t, SECP256K1_CMD_BYTES) \
    field(status, size_t) \
    field(cfg, size_t)
UJSON_SERDE_STRUCT(CryptoLibScaAsymSECP256K1SignOut, cryptolib_sca_asym_secp256k1_sign_out_t, CRYPTOLIBSCAASYM_SECP256K1_SIGN_OUT);

#define CRYPTOLIBSCAASYM_X25519_BASE_MUL_IN(field, string) \
    field(scalar, uint8_t, X25519_CMD_BYTES) \
    field(cfg, size_t) \
    field(num_iterations, size_t) \
    field(trigger, size_t)
UJSON_SERDE_STRUCT(CryptoLibScaAsymX25519BaseMulIn, cryptolib_sca_asym_x25519_base_mul_in_t, CRYPTOLIBSCAASYM_X25519_BASE_MUL_IN);

#define CRYPTOLIBSCAASYM_X25519_BASE_MUL_OUT(field, string) \
    field(x, uint8_t, X25519_CMD_BYTES) \
    field(y, uint8_t, X25519_CMD_BYTES) \
    field(status, size_t) \
    field(cfg, size_t)
UJSON_SERDE_STRUCT(CryptoLibScaAsymX25519BaseMulOut, cryptolib_sca_asym_x25519_base_mul_out_t, CRYPTOLIBSCAASYM_X25519_BASE_MUL_OUT);

#define CRYPTOLIBSCAASYM_X25519_POINT_MUL_IN(field, string) \
    field(scalar_alice, uint8_t, X25519_CMD_BYTES) \
    field(scalar_bob, uint8_t, X25519_CMD_BYTES) \
    field(cfg, size_t) \
    field(trigger, size_t)
UJSON_SERDE_STRUCT(CryptoLibScaAsymX25519PointMulIn, cryptolib_sca_asym_x25519_point_mul_in_t, CRYPTOLIBSCAASYM_X25519_POINT_MUL_IN);

#define CRYPTOLIBSCAASYM_X25519_POINT_MUL_OUT(field, string) \
    field(x, uint8_t, X25519_CMD_BYTES) \
    field(y, uint8_t, X25519_CMD_BYTES) \
    field(status, size_t) \
    field(cfg, size_t)
UJSON_SERDE_STRUCT(CryptoLibScaAsymX25519PointMulOut, cryptolib_sca_asym_x25519_point_mul_out_t, CRYPTOLIBSCAASYM_X25519_POINT_MUL_OUT);

#define CRYPTOLIBSCAASYM_X25519_ECDH_IN(field, string) \
    field(private_key, uint8_t, X25519_CMD_BYTES) \
    field(public_x, uint8_t, X25519_CMD_BYTES) \
    field(public_y, uint8_t, X25519_CMD_BYTES) \
    field(cfg, size_t) \
    field(trigger, size_t)
UJSON_SERDE_STRUCT(CryptoLibScaAsymX25519EcdhIn, cryptolib_sca_asym_x25519_ecdh_in_t, CRYPTOLIBSCAASYM_X25519_ECDH_IN);

#define CRYPTOLIBSCAASYM_X25519_ECDH_OUT(field, string) \
    field(shared_key, uint8_t, X25519_CMD_BYTES) \
    field(status, size_t) \
    field(cfg, size_t)
UJSON_SERDE_STRUCT(CryptoLibScaAsymX25519EcdhOut, cryptolib_sca_asym_x25519_ecdh_out_t, CRYPTOLIBSCAASYM_X25519_ECDH_OUT);

#define CRYPTOLIBSCAASYM_ED25519_BASE_MUL_IN(field, string) \
    field(scalar, uint8_t, ED25519_CMD_SCALAR_BYTES) \
    field(cfg, size_t) \
    field(num_iterations, size_t) \
    field(trigger, size_t)
UJSON_SERDE_STRUCT(CryptoLibScaAsymED25519BaseMulIn, cryptolib_sca_asym_ed25519_base_mul_in_t, CRYPTOLIBSCAASYM_ED25519_BASE_MUL_IN);

#define CRYPTOLIBSCAASYM_ED25519_BASE_MUL_OUT(field, string) \
    field(x, uint8_t, ED25519_CMD_SCALAR_BYTES) \
    field(y, uint8_t, ED25519_CMD_SCALAR_BYTES) \
    field(status, size_t) \
    field(cfg, size_t)
UJSON_SERDE_STRUCT(CryptoLibScaAsymED25519BaseMulOut, cryptolib_sca_asym_ed25519_base_mul_out_t, CRYPTOLIBSCAASYM_ED25519_BASE_MUL_OUT);

#define CRYPTOLIBSCAASYM_ED25519_SIGN_IN(field, string) \
    field(scalar, uint8_t, ED25519_CMD_SCALAR_BYTES) \
    field(message, uint8_t, ED25519_CMD_MAX_MSG_BYTES) \
    field(message_len, size_t) \
    field(cfg, size_t) \
    field(trigger, size_t)
UJSON_SERDE_STRUCT(CryptoLibScaAsymED25519SignIn, cryptolib_sca_asym_ed25519_sign_in_t, CRYPTOLIBSCAASYM_ED25519_SIGN_IN);

#define CRYPTOLIBSCAASYM_ED25519_SIGN_OUT(field, string) \
    field(r, uint8_t, ED25519_CMD_SIG_BYTES) \
    field(s, uint8_t, ED25519_CMD_SIG_BYTES) \
    field(pubx, uint8_t, ED25519_CMD_SCALAR_BYTES) \
    field(puby, uint8_t, ED25519_CMD_SCALAR_BYTES) \
    field(status, size_t) \
    field(cfg, size_t)
UJSON_SERDE_STRUCT(CryptoLibScaAsymED25519SignOut, cryptolib_sca_asym_ed25519_sign_out_t, CRYPTOLIBSCAASYM_ED25519_SIGN_OUT);

#undef MODULE_ID

// clang-format on

#ifdef __cplusplus
}
#endif
#endif  // OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_JSON_CRYPTOLIB_SCA_ASYM_COMMANDS_H_
