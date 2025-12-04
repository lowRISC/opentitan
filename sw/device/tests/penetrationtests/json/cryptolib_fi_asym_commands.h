// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_JSON_CRYPTOLIB_FI_ASYM_COMMANDS_H_
#define OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_JSON_CRYPTOLIB_FI_ASYM_COMMANDS_H_
#include "sw/device/lib/ujson/ujson_derive.h"
#ifdef __cplusplus
extern "C" {
#endif

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

#define CRYPTOLIBFIASYM_SUBCOMMAND(_, value) \
    value(_, RsaEnc) \
    value(_, RsaSign) \
    value(_, RsaVerify) \
    value(_, Prime) \
    value(_, P256BaseMul) \
    value(_, P256PointMul) \
    value(_, P256Ecdh) \
    value(_, P256Sign) \
    value(_, P256Verify) \
    value(_, P384BaseMul) \
    value(_, P384PointMul) \
    value(_, P384Ecdh) \
    value(_, P384Sign) \
    value(_, P384Verify) \
    value(_, Secp256k1BaseMul) \
    value(_, Secp256k1PointMul) \
    value(_, Secp256k1Ecdh) \
    value(_, Secp256k1Sign) \
    value(_, Secp256k1Verify) \
    value(_, X25519BaseMul) \
    value(_, X25519PointMul) \
    value(_, X25519Ecdh) \
    value(_, Ed25519BaseMul) \
    value(_, Ed25519Sign) \
    value(_, Ed25519Verify) \
    value(_, Init)
C_ONLY(UJSON_SERDE_ENUM(CryptoLibFiAsymSubcommand, cryptolib_fi_asym_subcommand_t, CRYPTOLIBFIASYM_SUBCOMMAND));
RUST_ONLY(UJSON_SERDE_ENUM(CryptoLibFiAsymSubcommand, cryptolib_fi_asym_subcommand_t, CRYPTOLIBFIASYM_SUBCOMMAND, RUST_DEFAULT_DERIVE, strum::EnumString));

#define CRYPTOLIBFIASYM_RSA_ENC_IN(field, string) \
    field(data, uint8_t, RSA_CMD_MAX_MESSAGE_BYTES) \
    field(data_len, size_t) \
    field(mode, size_t) \
    field(e, uint32_t) \
    field(n, uint8_t, RSA_CMD_MAX_N_BYTES) \
    field(d, uint8_t, RSA_CMD_MAX_N_BYTES) \
    field(n_len, size_t) \
    field(hashing, size_t) \
    field(padding, size_t) \
    field(op_enc, bool) \
    field(cfg, size_t) \
    field(trigger, size_t)
UJSON_SERDE_STRUCT(CryptoLibFiAsymRsaEncIn, cryptolib_fi_asym_rsa_enc_in_t, CRYPTOLIBFIASYM_RSA_ENC_IN);

#define CRYPTOLIBFIASYM_RSA_ENC_OUT(field, string) \
    field(n, uint8_t, RSA_CMD_MAX_N_BYTES) \
    field(d, uint8_t, RSA_CMD_MAX_N_BYTES) \
    field(n_len, size_t) \
    field(data, uint8_t, RSA_CMD_MAX_MESSAGE_BYTES) \
    field(data_len, size_t) \
    field(status, size_t) \
    field(alerts, uint32_t, 3) \
    field(loc_alerts, uint32_t) \
    field(err_status, uint32_t) \
    field(ast_alerts, uint32_t, 2) \
    field(cfg, size_t)
UJSON_SERDE_STRUCT(CryptoLibFiAsymRsaEncOut, cryptolib_fi_asym_rsa_enc_out_t, CRYPTOLIBFIASYM_RSA_ENC_OUT);

#define CRYPTOLIBFIASYM_RSA_SIGN_IN(field, string) \
    field(data, uint8_t, RSA_CMD_MAX_MESSAGE_BYTES) \
    field(data_len, size_t) \
    field(e, uint32_t) \
    field(n, uint8_t, RSA_CMD_MAX_N_BYTES) \
    field(d, uint8_t, RSA_CMD_MAX_N_BYTES) \
    field(n_len, size_t) \
    field(hashing, size_t) \
    field(padding, size_t) \
    field(cfg, size_t) \
    field(trigger, size_t)
UJSON_SERDE_STRUCT(CryptoLibFiAsymRsaSignIn, cryptolib_fi_asym_rsa_sign_in_t, CRYPTOLIBFIASYM_RSA_SIGN_IN);

#define CRYPTOLIBFIASYM_RSA_SIGN_OUT(field, string) \
    field(n, uint8_t, RSA_CMD_MAX_N_BYTES) \
    field(d, uint8_t, RSA_CMD_MAX_N_BYTES) \
    field(n_len, size_t) \
    field(sig, uint8_t, RSA_CMD_MAX_SIGNATURE_BYTES) \
    field(sig_len, size_t) \
    field(status, size_t) \
    field(alerts, uint32_t, 3) \
    field(loc_alerts, uint32_t) \
    field(err_status, uint32_t) \
    field(ast_alerts, uint32_t, 2) \
    field(cfg, size_t)
UJSON_SERDE_STRUCT(CryptoLibFiAsymRsaSignOut, cryptolib_fi_asym_rsa_sign_out_t, CRYPTOLIBFIASYM_RSA_SIGN_OUT);

#define CRYPTOLIBFIASYM_RSA_VERIFY_IN(field, string) \
    field(data, uint8_t, RSA_CMD_MAX_MESSAGE_BYTES) \
    field(data_len, size_t) \
    field(e, uint32_t) \
    field(n, uint8_t, RSA_CMD_MAX_N_BYTES) \
    field(n_len, size_t) \
    field(sig, uint8_t, RSA_CMD_MAX_SIGNATURE_BYTES) \
    field(sig_len, size_t) \
    field(hashing, size_t) \
    field(padding, size_t) \
    field(cfg, size_t) \
    field(trigger, size_t)
UJSON_SERDE_STRUCT(CryptoLibFiAsymRsaVerifyIn, cryptolib_fi_asym_rsa_verify_in_t, CRYPTOLIBFIASYM_RSA_VERIFY_IN);

#define CRYPTOLIBFIASYM_RSA_VERIFY_OUT(field, string) \
    field(result, bool) \
    field(status, size_t) \
    field(alerts, uint32_t, 3) \
    field(loc_alerts, uint32_t) \
    field(err_status, uint32_t) \
    field(ast_alerts, uint32_t, 2) \
    field(cfg, size_t)
UJSON_SERDE_STRUCT(CryptoLibFiAsymRsaVerifyOut, cryptolib_fi_asym_rsa_verify_out_t, CRYPTOLIBFIASYM_RSA_VERIFY_OUT);

#define CRYPTOLIBFIASYM_PRIME_IN(field, string) \
    field(e, uint32_t) \
    field(cfg, size_t) \
    field(trigger, size_t)
UJSON_SERDE_STRUCT(CryptoLibFiAsymPrimeIn, cryptolib_fi_asym_prime_in_t, CRYPTOLIBFIASYM_PRIME_IN);

#define CRYPTOLIBFIASYM_PRIME_OUT(field, string) \
    field(prime, uint8_t, RSA_CMD_MAX_N_BYTES) \
    field(prime_len, size_t) \
    field(status, size_t) \
    field(alerts, uint32_t, 3) \
    field(loc_alerts, uint32_t) \
    field(err_status, uint32_t) \
    field(ast_alerts, uint32_t, 2) \
    field(cfg, size_t)
UJSON_SERDE_STRUCT(CryptoLibFiAsymPrimeOut, cryptolib_fi_asym_prime_out_t, CRYPTOLIBFIASYM_PRIME_OUT);

#define CRYPTOLIBFIASYM_P256_BASE_MUL_IN(field, string) \
    field(scalar, uint8_t, P256_CMD_BYTES) \
    field(cfg, size_t) \
    field(trigger, size_t)
UJSON_SERDE_STRUCT(CryptoLibFiAsymP256BaseMulIn, cryptolib_fi_asym_p256_base_mul_in_t, CRYPTOLIBFIASYM_P256_BASE_MUL_IN);

#define CRYPTOLIBFIASYM_P256_BASE_MUL_OUT(field, string) \
    field(x, uint8_t, P256_CMD_BYTES) \
    field(y, uint8_t, P256_CMD_BYTES) \
    field(status, size_t) \
    field(alerts, uint32_t, 3) \
    field(loc_alerts, uint32_t) \
    field(err_status, uint32_t) \
    field(ast_alerts, uint32_t, 2) \
    field(cfg, size_t)
UJSON_SERDE_STRUCT(CryptoLibFiAsymP256BaseMulOut, cryptolib_fi_asym_p256_base_mul_out_t, CRYPTOLIBFIASYM_P256_BASE_MUL_OUT);

#define CRYPTOLIBFIASYM_P256_POINT_MUL_IN(field, string) \
    field(scalar_alice, uint8_t, P256_CMD_BYTES) \
    field(scalar_bob, uint8_t, P256_CMD_BYTES) \
    field(cfg, size_t) \
    field(trigger, size_t)
UJSON_SERDE_STRUCT(CryptoLibFiAsymP256PointMulIn, cryptolib_fi_asym_p256_point_mul_in_t, CRYPTOLIBFIASYM_P256_POINT_MUL_IN);

#define CRYPTOLIBFIASYM_P256_POINT_MUL_OUT(field, string) \
    field(x, uint8_t, P256_CMD_BYTES) \
    field(y, uint8_t, P256_CMD_BYTES) \
    field(status, size_t) \
    field(alerts, uint32_t, 3) \
    field(loc_alerts, uint32_t) \
    field(err_status, uint32_t) \
    field(ast_alerts, uint32_t, 2) \
    field(cfg, size_t)
UJSON_SERDE_STRUCT(CryptoLibFiAsymP256PointMulOut, cryptolib_fi_asym_p256_point_mul_out_t, CRYPTOLIBFIASYM_P256_POINT_MUL_OUT);

#define CRYPTOLIBFIASYM_P256_ECDH_IN(field, string) \
    field(private_key, uint8_t, P256_CMD_BYTES) \
    field(public_x, uint8_t, P256_CMD_BYTES) \
    field(public_y, uint8_t, P256_CMD_BYTES) \
    field(cfg, size_t) \
    field(trigger, size_t)
UJSON_SERDE_STRUCT(CryptoLibFiAsymP256EcdhIn, cryptolib_fi_asym_p256_ecdh_in_t, CRYPTOLIBFIASYM_P256_ECDH_IN);

#define CRYPTOLIBFIASYM_P256_ECDH_OUT(field, string) \
    field(shared_key, uint8_t, P256_CMD_BYTES) \
    field(status, size_t) \
    field(alerts, uint32_t, 3) \
    field(loc_alerts, uint32_t) \
    field(err_status, uint32_t) \
    field(ast_alerts, uint32_t, 2) \
    field(cfg, size_t)
UJSON_SERDE_STRUCT(CryptoLibFiAsymP256EcdhOut, cryptolib_fi_asym_p256_ecdh_out_t, CRYPTOLIBFIASYM_P256_ECDH_OUT);

#define CRYPTOLIBFIASYM_P256_SIGN_IN(field, string) \
    field(scalar, uint8_t, P256_CMD_BYTES) \
    field(pubx, uint8_t, P256_CMD_BYTES) \
    field(puby, uint8_t, P256_CMD_BYTES) \
    field(message, uint8_t, P256_CMD_BYTES) \
    field(cfg, size_t) \
    field(trigger, size_t)
UJSON_SERDE_STRUCT(CryptoLibFiAsymP256SignIn, cryptolib_fi_asym_p256_sign_in_t, CRYPTOLIBFIASYM_P256_SIGN_IN);

#define CRYPTOLIBFIASYM_P256_SIGN_OUT(field, string) \
    field(r, uint8_t, P256_CMD_BYTES) \
    field(s, uint8_t, P256_CMD_BYTES) \
    field(pubx, uint8_t, P256_CMD_BYTES) \
    field(puby, uint8_t, P256_CMD_BYTES) \
    field(status, size_t) \
    field(alerts, uint32_t, 3) \
    field(loc_alerts, uint32_t) \
    field(err_status, uint32_t) \
    field(ast_alerts, uint32_t, 2) \
    field(cfg, size_t)
UJSON_SERDE_STRUCT(CryptoLibFiAsymP256SignOut, cryptolib_fi_asym_p256_sign_out_t, CRYPTOLIBFIASYM_P256_SIGN_OUT);

#define CRYPTOLIBFIASYM_P256_VERIFY_IN(field, string) \
    field(pubx, uint8_t, P256_CMD_BYTES) \
    field(puby, uint8_t, P256_CMD_BYTES) \
    field(r, uint8_t, P256_CMD_BYTES) \
    field(s, uint8_t, P256_CMD_BYTES) \
    field(message, uint8_t, P256_CMD_BYTES) \
    field(cfg, size_t) \
    field(trigger, size_t)
UJSON_SERDE_STRUCT(CryptoLibFiAsymP256VerifyIn, cryptolib_fi_asym_p256_verify_in_t, CRYPTOLIBFIASYM_P256_VERIFY_IN);

#define CRYPTOLIBFIASYM_P256_VERIFY_OUT(field, string) \
    field(result, bool) \
    field(status, size_t) \
    field(alerts, uint32_t, 3) \
    field(loc_alerts, uint32_t) \
    field(err_status, uint32_t) \
    field(ast_alerts, uint32_t, 2) \
    field(cfg, size_t)
UJSON_SERDE_STRUCT(CryptoLibFiAsymP256VerifyOut, cryptolib_fi_asym_p256_verify_out_t, CRYPTOLIBFIASYM_P256_VERIFY_OUT);

#define CRYPTOLIBFIASYM_P384_BASE_MUL_IN(field, string) \
    field(scalar, uint8_t, P384_CMD_BYTES) \
    field(cfg, size_t) \
    field(trigger, size_t)
UJSON_SERDE_STRUCT(CryptoLibFiAsymP384BaseMulIn, cryptolib_fi_asym_p384_base_mul_in_t, CRYPTOLIBFIASYM_P384_BASE_MUL_IN);

#define CRYPTOLIBFIASYM_P384_BASE_MUL_OUT(field, string) \
    field(x, uint8_t, P384_CMD_BYTES) \
    field(y, uint8_t, P384_CMD_BYTES) \
    field(status, size_t) \
    field(alerts, uint32_t, 3) \
    field(loc_alerts, uint32_t) \
    field(err_status, uint32_t) \
    field(ast_alerts, uint32_t, 2) \
    field(cfg, size_t)
UJSON_SERDE_STRUCT(CryptoLibFiAsymP384BaseMulOut, cryptolib_fi_asym_p384_base_mul_out_t, CRYPTOLIBFIASYM_P384_BASE_MUL_OUT);

#define CRYPTOLIBFIASYM_P384_POINT_MUL_IN(field, string) \
    field(scalar_alice, uint8_t, P384_CMD_BYTES) \
    field(scalar_bob, uint8_t, P384_CMD_BYTES) \
    field(cfg, size_t) \
    field(trigger, size_t)
UJSON_SERDE_STRUCT(CryptoLibFiAsymP384PointMulIn, cryptolib_fi_asym_p384_point_mul_in_t, CRYPTOLIBFIASYM_P384_POINT_MUL_IN);

#define CRYPTOLIBFIASYM_P384_POINT_MUL_OUT(field, string) \
    field(x, uint8_t, P384_CMD_BYTES) \
    field(y, uint8_t, P384_CMD_BYTES) \
    field(status, size_t) \
    field(alerts, uint32_t, 3) \
    field(loc_alerts, uint32_t) \
    field(err_status, uint32_t) \
    field(ast_alerts, uint32_t, 2) \
    field(cfg, size_t)
UJSON_SERDE_STRUCT(CryptoLibFiAsymP384PointMulOut, cryptolib_fi_asym_p384_point_mul_out_t, CRYPTOLIBFIASYM_P384_POINT_MUL_OUT);

#define CRYPTOLIBFIASYM_P384_ECDH_IN(field, string) \
    field(private_key, uint8_t, P384_CMD_BYTES) \
    field(public_x, uint8_t, P384_CMD_BYTES) \
    field(public_y, uint8_t, P384_CMD_BYTES) \
    field(cfg, size_t) \
    field(trigger, size_t)
UJSON_SERDE_STRUCT(CryptoLibFiAsymP384EcdhIn, cryptolib_fi_asym_p384_ecdh_in_t, CRYPTOLIBFIASYM_P384_ECDH_IN);

#define CRYPTOLIBFIASYM_P384_ECDH_OUT(field, string) \
    field(shared_key, uint8_t, P384_CMD_BYTES) \
    field(status, size_t) \
    field(alerts, uint32_t, 3) \
    field(loc_alerts, uint32_t) \
    field(err_status, uint32_t) \
    field(ast_alerts, uint32_t, 2) \
    field(cfg, size_t)
UJSON_SERDE_STRUCT(CryptoLibFiAsymP384EcdhOut, cryptolib_fi_asym_p384_ecdh_out_t, CRYPTOLIBFIASYM_P384_ECDH_OUT);

#define CRYPTOLIBFIASYM_P384_SIGN_IN(field, string) \
    field(scalar, uint8_t, P384_CMD_BYTES) \
    field(pubx, uint8_t, P384_CMD_BYTES) \
    field(puby, uint8_t, P384_CMD_BYTES) \
    field(message, uint8_t, P384_CMD_BYTES) \
    field(cfg, size_t) \
    field(trigger, size_t)
UJSON_SERDE_STRUCT(CryptoLibFiAsymP384SignIn, cryptolib_fi_asym_p384_sign_in_t, CRYPTOLIBFIASYM_P384_SIGN_IN);

#define CRYPTOLIBFIASYM_P384_SIGN_OUT(field, string) \
    field(r, uint8_t, P384_CMD_BYTES) \
    field(s, uint8_t, P384_CMD_BYTES) \
    field(pubx, uint8_t, P384_CMD_BYTES) \
    field(puby, uint8_t, P384_CMD_BYTES) \
    field(status, size_t) \
    field(alerts, uint32_t, 3) \
    field(loc_alerts, uint32_t) \
    field(err_status, uint32_t) \
    field(ast_alerts, uint32_t, 2) \
    field(cfg, size_t)
UJSON_SERDE_STRUCT(CryptoLibFiAsymP384SignOut, cryptolib_fi_asym_p384_sign_out_t, CRYPTOLIBFIASYM_P384_SIGN_OUT);

#define CRYPTOLIBFIASYM_P384_VERIFY_IN(field, string) \
    field(pubx, uint8_t, P384_CMD_BYTES) \
    field(puby, uint8_t, P384_CMD_BYTES) \
    field(r, uint8_t, P384_CMD_BYTES) \
    field(s, uint8_t, P384_CMD_BYTES) \
    field(message, uint8_t, P384_CMD_BYTES) \
    field(cfg, size_t) \
    field(trigger, size_t)
UJSON_SERDE_STRUCT(CryptoLibFiAsymP384VerifyIn, cryptolib_fi_asym_p384_verify_in_t, CRYPTOLIBFIASYM_P384_VERIFY_IN);

#define CRYPTOLIBFIASYM_P384_VERIFY_OUT(field, string) \
    field(result, bool) \
    field(status, size_t) \
    field(alerts, uint32_t, 3) \
    field(loc_alerts, uint32_t) \
    field(err_status, uint32_t) \
    field(ast_alerts, uint32_t, 2) \
    field(cfg, size_t)
UJSON_SERDE_STRUCT(CryptoLibFiAsymP384VerifyOut, cryptolib_fi_asym_p384_verify_out_t, CRYPTOLIBFIASYM_P384_VERIFY_OUT);

#define CRYPTOLIBFIASYM_SECP256K1_BASE_MUL_IN(field, string) \
    field(scalar, uint8_t, SECP256K1_CMD_BYTES) \
    field(cfg, size_t) \
    field(trigger, size_t)
UJSON_SERDE_STRUCT(CryptoLibFiAsymSECP256K1BaseMulIn, cryptolib_fi_asym_secp256k1_base_mul_in_t, CRYPTOLIBFIASYM_SECP256K1_BASE_MUL_IN);

#define CRYPTOLIBFIASYM_SECP256K1_BASE_MUL_OUT(field, string) \
    field(x, uint8_t, SECP256K1_CMD_BYTES) \
    field(y, uint8_t, SECP256K1_CMD_BYTES) \
    field(status, size_t) \
    field(alerts, uint32_t, 3) \
    field(loc_alerts, uint32_t) \
    field(err_status, uint32_t) \
    field(ast_alerts, uint32_t, 2) \
    field(cfg, size_t)
UJSON_SERDE_STRUCT(CryptoLibFiAsymSECP256K1BaseMulOut, cryptolib_fi_asym_secp256k1_base_mul_out_t, CRYPTOLIBFIASYM_SECP256K1_BASE_MUL_OUT);

#define CRYPTOLIBFIASYM_SECP256K1_POINT_MUL_IN(field, string) \
    field(scalar_alice, uint8_t, SECP256K1_CMD_BYTES) \
    field(scalar_bob, uint8_t, SECP256K1_CMD_BYTES) \
    field(cfg, size_t) \
    field(trigger, size_t)
UJSON_SERDE_STRUCT(CryptoLibFiAsymSECP256K1PointMulIn, cryptolib_fi_asym_secp256k1_point_mul_in_t, CRYPTOLIBFIASYM_SECP256K1_POINT_MUL_IN);

#define CRYPTOLIBFIASYM_SECP256K1_POINT_MUL_OUT(field, string) \
    field(x, uint8_t, SECP256K1_CMD_BYTES) \
    field(y, uint8_t, SECP256K1_CMD_BYTES) \
    field(status, size_t) \
    field(alerts, uint32_t, 3) \
    field(loc_alerts, uint32_t) \
    field(err_status, uint32_t) \
    field(ast_alerts, uint32_t, 2) \
    field(cfg, size_t)
UJSON_SERDE_STRUCT(CryptoLibFiAsymSECP256K1PointMulOut, cryptolib_fi_asym_secp256k1_point_mul_out_t, CRYPTOLIBFIASYM_SECP256K1_POINT_MUL_OUT);

#define CRYPTOLIBFIASYM_SECP256K1_ECDH_IN(field, string) \
    field(private_key, uint8_t, SECP256K1_CMD_BYTES) \
    field(public_x, uint8_t, SECP256K1_CMD_BYTES) \
    field(public_y, uint8_t, SECP256K1_CMD_BYTES) \
    field(cfg, size_t) \
    field(trigger, size_t)
UJSON_SERDE_STRUCT(CryptoLibFiAsymSECP256K1EcdhIn, cryptolib_fi_asym_secp256k1_ecdh_in_t, CRYPTOLIBFIASYM_SECP256K1_ECDH_IN);

#define CRYPTOLIBFIASYM_SECP256K1_ECDH_OUT(field, string) \
    field(shared_key, uint8_t, SECP256K1_CMD_BYTES) \
    field(status, size_t) \
    field(alerts, uint32_t, 3) \
    field(loc_alerts, uint32_t) \
    field(err_status, uint32_t) \
    field(ast_alerts, uint32_t, 2) \
    field(cfg, size_t)
UJSON_SERDE_STRUCT(CryptoLibFiAsymSECP256K1EcdhOut, cryptolib_fi_asym_secp256k1_ecdh_out_t, CRYPTOLIBFIASYM_SECP256K1_ECDH_OUT);

#define CRYPTOLIBFIASYM_SECP256K1_SIGN_IN(field, string) \
    field(scalar, uint8_t, SECP256K1_CMD_BYTES) \
    field(message, uint8_t, SECP256K1_CMD_BYTES) \
    field(cfg, size_t) \
    field(trigger, size_t)
UJSON_SERDE_STRUCT(CryptoLibFiAsymSECP256K1SignIn, cryptolib_fi_asym_secp256k1_sign_in_t, CRYPTOLIBFIASYM_SECP256K1_SIGN_IN);

#define CRYPTOLIBFIASYM_SECP256K1_SIGN_OUT(field, string) \
    field(r, uint8_t, SECP256K1_CMD_BYTES) \
    field(s, uint8_t, SECP256K1_CMD_BYTES) \
    field(pubx, uint8_t, SECP256K1_CMD_BYTES) \
    field(puby, uint8_t, SECP256K1_CMD_BYTES) \
    field(status, size_t) \
    field(alerts, uint32_t, 3) \
    field(loc_alerts, uint32_t) \
    field(err_status, uint32_t) \
    field(ast_alerts, uint32_t, 2) \
    field(cfg, size_t)
UJSON_SERDE_STRUCT(CryptoLibFiAsymSECP256K1SignOut, cryptolib_fi_asym_secp256k1_sign_out_t, CRYPTOLIBFIASYM_SECP256K1_SIGN_OUT);

#define CRYPTOLIBFIASYM_SECP256K1_VERIFY_IN(field, string) \
    field(pubx, uint8_t, SECP256K1_CMD_BYTES) \
    field(puby, uint8_t, SECP256K1_CMD_BYTES) \
    field(r, uint8_t, SECP256K1_CMD_BYTES) \
    field(s, uint8_t, SECP256K1_CMD_BYTES) \
    field(message, uint8_t, SECP256K1_CMD_BYTES) \
    field(cfg, size_t) \
    field(trigger, size_t)
UJSON_SERDE_STRUCT(CryptoLibFiAsymSECP256K1VerifyIn, cryptolib_fi_asym_secp256k1_verify_in_t, CRYPTOLIBFIASYM_SECP256K1_VERIFY_IN);

#define CRYPTOLIBFIASYM_SECP256K1_VERIFY_OUT(field, string) \
    field(result, bool) \
    field(status, size_t) \
    field(alerts, uint32_t, 3) \
    field(loc_alerts, uint32_t) \
    field(err_status, uint32_t) \
    field(ast_alerts, uint32_t, 2) \
    field(cfg, size_t)
UJSON_SERDE_STRUCT(CryptoLibFiAsymSECP256K1VerifyOut, cryptolib_fi_asym_secp256k1_verify_out_t, CRYPTOLIBFIASYM_SECP256K1_VERIFY_OUT);

#define CRYPTOLIBFIASYM_X25519_BASE_MUL_IN(field, string) \
    field(scalar, uint8_t, X25519_CMD_BYTES) \
    field(cfg, size_t) \
    field(trigger, size_t)
UJSON_SERDE_STRUCT(CryptoLibFiAsymX25519BaseMulIn, cryptolib_fi_asym_x25519_base_mul_in_t, CRYPTOLIBFIASYM_X25519_BASE_MUL_IN);

#define CRYPTOLIBFIASYM_X25519_BASE_MUL_OUT(field, string) \
    field(x, uint8_t, X25519_CMD_BYTES) \
    field(y, uint8_t, X25519_CMD_BYTES) \
    field(status, size_t) \
    field(alerts, uint32_t, 3) \
    field(loc_alerts, uint32_t) \
    field(err_status, uint32_t) \
    field(ast_alerts, uint32_t, 2) \
    field(cfg, size_t)
UJSON_SERDE_STRUCT(CryptoLibFiAsymX25519BaseMulOut, cryptolib_fi_asym_x25519_base_mul_out_t, CRYPTOLIBFIASYM_X25519_BASE_MUL_OUT);

#define CRYPTOLIBFIASYM_X25519_POINT_MUL_IN(field, string) \
    field(scalar_alice, uint8_t, X25519_CMD_BYTES) \
    field(scalar_bob, uint8_t, X25519_CMD_BYTES) \
    field(cfg, size_t) \
    field(trigger, size_t)
UJSON_SERDE_STRUCT(CryptoLibFiAsymX25519PointMulIn, cryptolib_fi_asym_x25519_point_mul_in_t, CRYPTOLIBFIASYM_X25519_POINT_MUL_IN);

#define CRYPTOLIBFIASYM_X25519_POINT_MUL_OUT(field, string) \
    field(x, uint8_t, X25519_CMD_BYTES) \
    field(y, uint8_t, X25519_CMD_BYTES) \
    field(status, size_t) \
    field(alerts, uint32_t, 3) \
    field(loc_alerts, uint32_t) \
    field(err_status, uint32_t) \
    field(ast_alerts, uint32_t, 2) \
    field(cfg, size_t)
UJSON_SERDE_STRUCT(CryptoLibFiAsymX25519PointMulOut, cryptolib_fi_asym_x25519_point_mul_out_t, CRYPTOLIBFIASYM_X25519_POINT_MUL_OUT);

#define CRYPTOLIBFIASYM_X25519_ECDH_IN(field, string) \
    field(private_key, uint8_t, X25519_CMD_BYTES) \
    field(public_x, uint8_t, X25519_CMD_BYTES) \
    field(public_y, uint8_t, X25519_CMD_BYTES) \
    field(cfg, size_t) \
    field(trigger, size_t)
UJSON_SERDE_STRUCT(CryptoLibFiAsymX25519EcdhIn, cryptolib_fi_asym_x25519_ecdh_in_t, CRYPTOLIBFIASYM_X25519_ECDH_IN);

#define CRYPTOLIBFIASYM_X25519_ECDH_OUT(field, string) \
    field(shared_key, uint8_t, X25519_CMD_BYTES) \
    field(status, size_t) \
    field(alerts, uint32_t, 3) \
    field(loc_alerts, uint32_t) \
    field(err_status, uint32_t) \
    field(ast_alerts, uint32_t, 2) \
    field(cfg, size_t)
UJSON_SERDE_STRUCT(CryptoLibFiAsymX25519EcdhOut, cryptolib_fi_asym_x25519_ecdh_out_t, CRYPTOLIBFIASYM_X25519_ECDH_OUT);

#define CRYPTOLIBFIASYM_ED25519_BASE_MUL_IN(field, string) \
    field(scalar, uint8_t, ED25519_CMD_SCALAR_BYTES) \
    field(cfg, size_t) \
    field(trigger, size_t)
UJSON_SERDE_STRUCT(CryptoLibFiAsymED25519BaseMulIn, cryptolib_fi_asym_ed25519_base_mul_in_t, CRYPTOLIBFIASYM_ED25519_BASE_MUL_IN);

#define CRYPTOLIBFIASYM_ED25519_BASE_MUL_OUT(field, string) \
    field(x, uint8_t, ED25519_CMD_SCALAR_BYTES) \
    field(y, uint8_t, ED25519_CMD_SCALAR_BYTES) \
    field(status, size_t) \
    field(alerts, uint32_t, 3) \
    field(loc_alerts, uint32_t) \
    field(err_status, uint32_t) \
    field(ast_alerts, uint32_t, 2) \
    field(cfg, size_t)
UJSON_SERDE_STRUCT(CryptoLibFiAsymED25519BaseMulOut, cryptolib_fi_asym_ed25519_base_mul_out_t, CRYPTOLIBFIASYM_ED25519_BASE_MUL_OUT);

#define CRYPTOLIBFIASYM_ED25519_SIGN_IN(field, string) \
    field(scalar, uint8_t, ED25519_CMD_SCALAR_BYTES) \
    field(message, uint8_t, ED25519_CMD_MAX_MSG_BYTES) \
    field(message_len, size_t) \
    field(cfg, size_t) \
    field(trigger, size_t)
UJSON_SERDE_STRUCT(CryptoLibFiAsymED25519SignIn, cryptolib_fi_asym_ed25519_sign_in_t, CRYPTOLIBFIASYM_ED25519_SIGN_IN);

#define CRYPTOLIBFIASYM_ED25519_SIGN_OUT(field, string) \
    field(r, uint8_t, ED25519_CMD_SIG_BYTES) \
    field(s, uint8_t, ED25519_CMD_SIG_BYTES) \
    field(pubx, uint8_t, ED25519_CMD_SCALAR_BYTES) \
    field(puby, uint8_t, ED25519_CMD_SCALAR_BYTES) \
    field(status, size_t) \
    field(alerts, uint32_t, 3) \
    field(loc_alerts, uint32_t) \
    field(err_status, uint32_t) \
    field(ast_alerts, uint32_t, 2) \
    field(cfg, size_t)
UJSON_SERDE_STRUCT(CryptoLibFiAsymED25519SignOut, cryptolib_fi_asym_ed25519_sign_out_t, CRYPTOLIBFIASYM_ED25519_SIGN_OUT);

#define CRYPTOLIBFIASYM_ED25519_VERIFY_IN(field, string) \
    field(pubx, uint8_t, ED25519_CMD_SCALAR_BYTES) \
    field(puby, uint8_t, ED25519_CMD_SCALAR_BYTES) \
    field(r, uint8_t, ED25519_CMD_SIG_BYTES) \
    field(s, uint8_t, ED25519_CMD_SIG_BYTES) \
    field(message, uint8_t, ED25519_CMD_MAX_MSG_BYTES) \
    field(message_len, size_t) \
    field(cfg, size_t) \
    field(trigger, size_t)
UJSON_SERDE_STRUCT(CryptoLibFiAsymED25519VerifyIn, cryptolib_fi_asym_ed25519_verify_in_t, CRYPTOLIBFIASYM_ED25519_VERIFY_IN);

#define CRYPTOLIBFIASYM_ED25519_VERIFY_OUT(field, string) \
    field(result, bool) \
    field(status, size_t) \
    field(alerts, uint32_t, 3) \
    field(loc_alerts, uint32_t) \
    field(err_status, uint32_t) \
    field(ast_alerts, uint32_t, 2) \
    field(cfg, size_t)
UJSON_SERDE_STRUCT(CryptoLibFiAsymED25519VerifyOut, cryptolib_fi_asym_ed25519_verify_out_t, CRYPTOLIBFIASYM_ED25519_VERIFY_OUT);

// clang-format on

#ifdef __cplusplus
}
#endif
#endif  // OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_JSON_CRYPTOLIB_FI_ASYM_COMMANDS_H_
