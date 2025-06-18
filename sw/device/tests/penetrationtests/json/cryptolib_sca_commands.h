// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_JSON_CRYPTOLIB_SCA_COMMANDS_H_
#define OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_JSON_CRYPTOLIB_SCA_COMMANDS_H_
#include "sw/device/lib/ujson/ujson_derive.h"
#ifdef __cplusplus
extern "C" {
#endif

#define AES_CMD_MAX_MSG_BYTES 64
#define AES_CMD_MAX_KEY_BYTES 32
#define AES_CMD_MAX_BLOCK_BYTES 16

#define TDES_CMD_MAX_MSG_BYTES 64
#define TDES_CMD_MAX_KEY_BYTES 21
#define TDES_CMD_MAX_BLOCK_BYTES 8

#define HMAC_CMD_MAX_MSG_BYTES 64
#define HMAC_CMD_MAX_KEY_BYTES 192
#define HMAC_CMD_MAX_TAG_BYTES 64

#define DRBG_CMD_MAX_ENTROPY_BYTES 32
#define DRBG_CMD_MAX_NONCE_BYTES 16
#define DRBG_CMD_MAX_OUTPUT_BYTES 256

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

#define CRYPTOLIBSCA_SUBCOMMAND(_, value) \
    value(_, AesFvsrPlaintext) \
    value(_, AesFvsrKey) \
    value(_, CmacFvsrPlaintext) \
    value(_, CmacFvsrKey) \
    value(_, GcmFvsrPlaintext) \
    value(_, GcmFvsrKey) \
    value(_, TdesFvsrPlaintext) \
    value(_, TdesFvsrKey) \
    value(_, HmacFvsrPlaintext) \
    value(_, HmacFvsrKey) \
    value(_, DrbgFvsr) \
    value(_, RsaDec) \
    value(_, RsaSign) \
    value(_, Prime) \
    value(_, P256BaseMul) \
    value(_, P256PointMul) \
    value(_, P256Sign) \
    value(_, P384BaseMul) \
    value(_, P384PointMul) \
    value(_, P384Sign) \
    value(_, Secp256k1BaseMul) \
    value(_, Secp256k1PointMul) \
    value(_, Secp256k1Sign) \
    value(_, X25519BaseMul) \
    value(_, X25519PointMul) \
    value(_, Ed25519BaseMul) \
    value(_, Ed25519Sign) \
    value(_, Init)
C_ONLY(UJSON_SERDE_ENUM(CryptoLibScaSubcommand, cryptolib_sca_subcommand_t, CRYPTOLIBSCA_SUBCOMMAND));
RUST_ONLY(UJSON_SERDE_ENUM(CryptoLibScaSubcommand, cryptolib_sca_subcommand_t, CRYPTOLIBSCA_SUBCOMMAND, RUST_DEFAULT_DERIVE, strum::EnumString));

#define CRYPTOLIBSCA_AES_IN(field, string) \
    field(data, uint8_t, AES_CMD_MAX_MSG_BYTES) \
    field(data_len, size_t) \
    field(key, uint8_t, AES_CMD_MAX_KEY_BYTES) \
    field(key_len, size_t) \
    field(iv, uint8_t, AES_CMD_MAX_BLOCK_BYTES) \
    field(padding, size_t) \
    field(mode, size_t) \
    field(op_enc, bool) \
    field(cfg, size_t) \
    field(num_iterations, size_t) \
    field(trigger, size_t)
UJSON_SERDE_STRUCT(CryptoLibScaAesIn, cryptolib_sca_aes_in_t, CRYPTOLIBSCA_AES_IN);

#define CRYPTOLIBSCA_AES_IN_FVSR_KEY(field, string) \
    field(data_len, size_t) \
    field(key, uint8_t, AES_CMD_MAX_KEY_BYTES) \
    field(key_len, size_t) \
    field(iv, uint8_t, AES_CMD_MAX_BLOCK_BYTES) \
    field(padding, size_t) \
    field(mode, size_t) \
    field(op_enc, bool) \
    field(cfg, size_t) \
    field(num_iterations, size_t) \
    field(trigger, size_t)
UJSON_SERDE_STRUCT(CryptoLibScaAesInFvsrKey, cryptolib_sca_aes_in_fvsr_key_t, CRYPTOLIBSCA_AES_IN_FVSR_KEY);

#define CRYPTOLIBSCA_AES_OUT(field, string) \
    field(data, uint8_t, AES_CMD_MAX_MSG_BYTES) \
    field(data_len, size_t) \
    field(cfg, size_t)
UJSON_SERDE_STRUCT(CryptoLibScaAesOut, cryptolib_sca_aes_out_t, CRYPTOLIBSCA_AES_OUT);

#define CRYPTOLIBSCA_CMAC_IN(field, string) \
    field(data, uint8_t, AES_CMD_MAX_MSG_BYTES) \
    field(data_len, size_t) \
    field(key, uint8_t, AES_CMD_MAX_KEY_BYTES) \
    field(key_len, size_t) \
    field(iv, uint8_t, AES_CMD_MAX_BLOCK_BYTES) \
    field(cfg, size_t) \
    field(num_iterations, size_t) \
    field(trigger, size_t)
UJSON_SERDE_STRUCT(CryptoLibScaCmacIn, cryptolib_sca_cmac_in_t, CRYPTOLIBSCA_CMAC_IN);

#define CRYPTOLIBSCA_CMAC_IN_FVSR_KEY(field, string) \
    field(data_len, size_t) \
    field(key, uint8_t, AES_CMD_MAX_KEY_BYTES) \
    field(key_len, size_t) \
    field(iv, uint8_t, AES_CMD_MAX_BLOCK_BYTES) \
    field(cfg, size_t) \
    field(num_iterations, size_t) \
    field(trigger, size_t)
UJSON_SERDE_STRUCT(CryptoLibScaCmacInFvsrKey, cryptolib_sca_cmac_in_fvsr_key_t, CRYPTOLIBSCA_CMAC_IN_FVSR_KEY);

#define CRYPTOLIBSCA_CMAC_OUT(field, string) \
    field(data, uint8_t, AES_CMD_MAX_MSG_BYTES) \
    field(data_len, size_t) \
    field(cfg, size_t)
UJSON_SERDE_STRUCT(CryptoLibScaCmacOut, cryptolib_sca_cmac_out_t, CRYPTOLIBSCA_CMAC_OUT);

#define CRYPTOLIBSCA_GCM_IN(field, string) \
    field(data, uint8_t, AES_CMD_MAX_MSG_BYTES) \
    field(data_len, size_t) \
    field(aad, uint8_t, AES_CMD_MAX_MSG_BYTES) \
    field(aad_len, size_t) \
    field(key, uint8_t, AES_CMD_MAX_KEY_BYTES) \
    field(key_len, size_t) \
    field(iv, uint8_t, AES_CMD_MAX_BLOCK_BYTES) \
    field(cfg, size_t) \
    field(num_iterations, size_t) \
    field(trigger, size_t)
UJSON_SERDE_STRUCT(CryptoLibScaGcmIn, cryptolib_sca_gcm_in_t, CRYPTOLIBSCA_GCM_IN);

#define CRYPTOLIBSCA_GCM_IN_FVSR_KEY(field, string) \
    field(data_len, size_t) \
    field(aad, uint8_t, AES_CMD_MAX_MSG_BYTES) \
    field(aad_len, size_t) \
    field(key, uint8_t, AES_CMD_MAX_KEY_BYTES) \
    field(key_len, size_t) \
    field(iv, uint8_t, AES_CMD_MAX_BLOCK_BYTES) \
    field(cfg, size_t) \
    field(num_iterations, size_t) \
    field(trigger, size_t)
UJSON_SERDE_STRUCT(CryptoLibScaGcmInFvsrKey, cryptolib_sca_gcm_in_fvsr_key_t, CRYPTOLIBSCA_GCM_IN_FVSR_KEY);

#define CRYPTOLIBSCA_GCM_OUT(field, string) \
    field(data, uint8_t, AES_CMD_MAX_MSG_BYTES) \
    field(data_len, uint32_t) \
    field(tag, uint8_t, AES_CMD_MAX_MSG_BYTES) \
    field(tag_len, uint32_t) \
    field(cfg, size_t)
UJSON_SERDE_STRUCT(CryptoLibScaGcmOut, cryptolib_sca_gcm_out_t, CRYPTOLIBSCA_GCM_OUT);

#define CRYPTOLIBSCA_TDES_IN(field, string) \
    field(data, uint8_t, TDES_CMD_MAX_MSG_BYTES) \
    field(data_len, size_t) \
    field(key, uint8_t, TDES_CMD_MAX_KEY_BYTES) \
    field(key_len, size_t) \
    field(iv, uint8_t, TDES_CMD_MAX_BLOCK_BYTES) \
    field(padding, size_t) \
    field(mode, size_t) \
    field(op_enc, bool) \
    field(cfg, size_t) \
    field(num_iterations, size_t) \
    field(trigger, size_t)
UJSON_SERDE_STRUCT(CryptoLibScaTdesIn, cryptolib_sca_tdes_in_t, CRYPTOLIBSCA_TDES_IN);

#define CRYPTOLIBSCA_TDES_IN_FVSR_KEY(field, string) \
    field(data_len, size_t) \
    field(key, uint8_t, TDES_CMD_MAX_KEY_BYTES) \
    field(key_len, size_t) \
    field(iv, uint8_t, TDES_CMD_MAX_BLOCK_BYTES) \
    field(padding, size_t) \
    field(mode, size_t) \
    field(op_enc, bool) \
    field(cfg, size_t) \
    field(num_iterations, size_t) \
    field(trigger, size_t)
UJSON_SERDE_STRUCT(CryptoLibScaTdesInFvsrKey, cryptolib_sca_tdes_in_fvsr_key_t, CRYPTOLIBSCA_TDES_IN_FVSR_KEY);

#define CRYPTOLIBSCA_TDES_OUT(field, string) \
    field(data, uint8_t, TDES_CMD_MAX_MSG_BYTES) \
    field(data_len, size_t) \
    field(cfg, size_t)
UJSON_SERDE_STRUCT(CryptoLibScaTdesOut, cryptolib_sca_tdes_out_t, CRYPTOLIBSCA_TDES_OUT);

#define CRYPTOLIBSCA_HMAC_IN(field, string) \
    field(data, uint8_t, HMAC_CMD_MAX_MSG_BYTES) \
    field(data_len, size_t) \
    field(key, uint8_t, HMAC_CMD_MAX_KEY_BYTES) \
    field(key_len, size_t) \
    field(padding, size_t) \
    field(mode, size_t) \
    field(cfg, size_t) \
    field(num_iterations, size_t) \
    field(trigger, size_t)
UJSON_SERDE_STRUCT(CryptoLibScaHmacIn, cryptolib_sca_hmac_in_t, CRYPTOLIBSCA_HMAC_IN);

#define CRYPTOLIBSCA_HMAC_IN_FVSR_KEY(field, string) \
    field(data_len, size_t) \
    field(key, uint8_t, HMAC_CMD_MAX_KEY_BYTES) \
    field(key_len, size_t) \
    field(padding, size_t) \
    field(mode, size_t) \
    field(cfg, size_t) \
    field(num_iterations, size_t) \
    field(trigger, size_t)
UJSON_SERDE_STRUCT(CryptoLibScaHmacInFvsrKey, cryptolib_sca_hmac_in_fvsr_key_t, CRYPTOLIBSCA_HMAC_IN_FVSR_KEY);

#define CRYPTOLIBSCA_HMAC_OUT(field, string) \
    field(data, uint8_t, HMAC_CMD_MAX_TAG_BYTES) \
    field(data_len, size_t) \
    field(cfg, size_t)
UJSON_SERDE_STRUCT(CryptoLibScaHmacOut, cryptolib_sca_hmac_out_t, CRYPTOLIBSCA_HMAC_OUT);

#define CRYPTOLIBSCA_DRBG_IN(field, string) \
    field(entropy, uint8_t, DRBG_CMD_MAX_ENTROPY_BYTES) \
    field(entropy_len, size_t) \
    field(nonce_len, size_t) \
    field(reseed_interval, size_t) \
    field(mode, size_t) \
    field(cfg, size_t) \
    field(num_iterations, size_t) \
    field(trigger, size_t)
UJSON_SERDE_STRUCT(CryptoLibScaDrbgIn, cryptolib_sca_drbg_in_t, CRYPTOLIBSCA_DRBG_IN);

#define CRYPTOLIBSCA_DRBG_OUT(field, string) \
    field(data, uint8_t, DRBG_CMD_MAX_OUTPUT_BYTES) \
    field(data_len, size_t) \
    field(cfg, size_t)
UJSON_SERDE_STRUCT(CryptoLibScaDrbgOut, cryptolib_sca_drbg_out_t, CRYPTOLIBSCA_DRBG_OUT);

#define CRYPTOLIBSCA_RSA_DEC_IN(field, string) \
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
UJSON_SERDE_STRUCT(CryptoLibScaRsaDecIn, cryptolib_sca_rsa_dec_in_t, CRYPTOLIBSCA_RSA_DEC_IN);

#define CRYPTOLIBSCA_RSA_DEC_OUT(field, string) \
    field(n, uint8_t, RSA_CMD_MAX_N_BYTES) \
    field(d, uint8_t, RSA_CMD_MAX_N_BYTES) \
    field(n_len, size_t) \
    field(data, uint8_t, RSA_CMD_MAX_MESSAGE_BYTES) \
    field(data_len, size_t) \
    field(cfg, size_t)
UJSON_SERDE_STRUCT(CryptoLibScaRsaDecOut, cryptolib_sca_rsa_dec_out_t, CRYPTOLIBSCA_RSA_DEC_OUT);

#define CRYPTOLIBSCA_RSA_SIGN_IN(field, string) \
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
UJSON_SERDE_STRUCT(CryptoLibScaRsaSignIn, cryptolib_sca_rsa_sign_in_t, CRYPTOLIBSCA_RSA_SIGN_IN);

#define CRYPTOLIBSCA_RSA_SIGN_OUT(field, string) \
    field(n, uint8_t, RSA_CMD_MAX_N_BYTES) \
    field(d, uint8_t, RSA_CMD_MAX_N_BYTES) \
    field(n_len, size_t) \
    field(sig, uint8_t, RSA_CMD_MAX_SIGNATURE_BYTES) \
    field(sig_len, size_t) \
    field(cfg, size_t)
UJSON_SERDE_STRUCT(CryptoLibScaRsaSignOut, cryptolib_sca_rsa_sign_out_t, CRYPTOLIBSCA_RSA_SIGN_OUT);

#define CRYPTOLIBSCA_PRIME_IN(field, string) \
    field(e, uint32_t) \
    field(cfg, size_t) \
    field(trigger, size_t)
UJSON_SERDE_STRUCT(CryptoLibScaPrimeIn, cryptolib_sca_prime_in_t, CRYPTOLIBSCA_PRIME_IN);

#define CRYPTOLIBSCA_PRIME_OUT(field, string) \
    field(prime, uint8_t, RSA_CMD_MAX_N_BYTES) \
    field(prime_len, size_t) \
    field(cfg, size_t)
UJSON_SERDE_STRUCT(CryptoLibScaPrimeOut, cryptolib_sca_prime_out_t, CRYPTOLIBSCA_PRIME_OUT);

#define CRYPTOLIBSCA_P256_BASE_MUL_IN(field, string) \
    field(scalar, uint8_t, P256_CMD_BYTES) \
    field(cfg, size_t) \
    field(trigger, size_t)
UJSON_SERDE_STRUCT(CryptoLibScaP256BaseMulIn, cryptolib_sca_p256_base_mul_in_t, CRYPTOLIBSCA_P256_BASE_MUL_IN);

#define CRYPTOLIBSCA_P256_BASE_MUL_OUT(field, string) \
    field(x, uint8_t, P256_CMD_BYTES) \
    field(y, uint8_t, P256_CMD_BYTES) \
    field(cfg, size_t)
UJSON_SERDE_STRUCT(CryptoLibScaP256BaseMulOut, cryptolib_sca_p256_base_mul_out_t, CRYPTOLIBSCA_P256_BASE_MUL_OUT);

#define CRYPTOLIBSCA_P256_POINT_MUL_IN(field, string) \
    field(scalar_alice, uint8_t, P256_CMD_BYTES) \
    field(scalar_bob, uint8_t, P256_CMD_BYTES) \
    field(cfg, size_t) \
    field(trigger, size_t)
UJSON_SERDE_STRUCT(CryptoLibScaP256PointMulIn, cryptolib_sca_p256_point_mul_in_t, CRYPTOLIBSCA_P256_POINT_MUL_IN);

#define CRYPTOLIBSCA_P256_POINT_MUL_OUT(field, string) \
    field(x, uint8_t, P256_CMD_BYTES) \
    field(y, uint8_t, P256_CMD_BYTES) \
    field(cfg, size_t)
UJSON_SERDE_STRUCT(CryptoLibScaP256PointMulOut, cryptolib_sca_p256_point_mul_out_t, CRYPTOLIBSCA_P256_POINT_MUL_OUT);

#define CRYPTOLIBSCA_P256_SIGN_IN(field, string) \
    field(scalar, uint8_t, P256_CMD_BYTES) \
    field(message, uint8_t, P256_CMD_BYTES) \
    field(cfg, size_t) \
    field(trigger, size_t)
UJSON_SERDE_STRUCT(CryptoLibScaP256SignIn, cryptolib_sca_p256_sign_in_t, CRYPTOLIBSCA_P256_SIGN_IN);

#define CRYPTOLIBSCA_P256_SIGN_OUT(field, string) \
    field(r, uint8_t, P256_CMD_BYTES) \
    field(s, uint8_t, P256_CMD_BYTES) \
    field(pubx, uint8_t, P256_CMD_BYTES) \
    field(puby, uint8_t, P256_CMD_BYTES) \
    field(cfg, size_t)
UJSON_SERDE_STRUCT(CryptoLibScaP256SignOut, cryptolib_sca_p256_sign_out_t, CRYPTOLIBSCA_P256_SIGN_OUT);

#define CRYPTOLIBSCA_P384_BASE_MUL_IN(field, string) \
    field(scalar, uint8_t, P384_CMD_BYTES) \
    field(cfg, size_t) \
    field(trigger, size_t)
UJSON_SERDE_STRUCT(CryptoLibScaP384BaseMulIn, cryptolib_sca_p384_base_mul_in_t, CRYPTOLIBSCA_P384_BASE_MUL_IN);

#define CRYPTOLIBSCA_P384_BASE_MUL_OUT(field, string) \
    field(x, uint8_t, P384_CMD_BYTES) \
    field(y, uint8_t, P384_CMD_BYTES) \
    field(cfg, size_t)
UJSON_SERDE_STRUCT(CryptoLibScaP384BaseMulOut, cryptolib_sca_p384_base_mul_out_t, CRYPTOLIBSCA_P384_BASE_MUL_OUT);

#define CRYPTOLIBSCA_P384_POINT_MUL_IN(field, string) \
    field(scalar_alice, uint8_t, P384_CMD_BYTES) \
    field(scalar_bob, uint8_t, P384_CMD_BYTES) \
    field(cfg, size_t) \
    field(trigger, size_t)
UJSON_SERDE_STRUCT(CryptoLibScaP384PointMulIn, cryptolib_sca_p384_point_mul_in_t, CRYPTOLIBSCA_P384_POINT_MUL_IN);

#define CRYPTOLIBSCA_P384_POINT_MUL_OUT(field, string) \
    field(x, uint8_t, P384_CMD_BYTES) \
    field(y, uint8_t, P384_CMD_BYTES) \
    field(cfg, size_t)
UJSON_SERDE_STRUCT(CryptoLibScaP384PointMulOut, cryptolib_sca_p384_point_mul_out_t, CRYPTOLIBSCA_P384_POINT_MUL_OUT);

#define CRYPTOLIBSCA_P384_SIGN_IN(field, string) \
    field(scalar, uint8_t, P384_CMD_BYTES) \
    field(message, uint8_t, P384_CMD_BYTES) \
    field(cfg, size_t) \
    field(trigger, size_t)
UJSON_SERDE_STRUCT(CryptoLibScaP384SignIn, cryptolib_sca_p384_sign_in_t, CRYPTOLIBSCA_P384_SIGN_IN);

#define CRYPTOLIBSCA_P384_SIGN_OUT(field, string) \
    field(r, uint8_t, P384_CMD_BYTES) \
    field(s, uint8_t, P384_CMD_BYTES) \
    field(pubx, uint8_t, P384_CMD_BYTES) \
    field(puby, uint8_t, P384_CMD_BYTES) \
    field(cfg, size_t)
UJSON_SERDE_STRUCT(CryptoLibScaP384SignOut, cryptolib_sca_p384_sign_out_t, CRYPTOLIBSCA_P384_SIGN_OUT);

#define CRYPTOLIBSCA_SECP256K1_BASE_MUL_IN(field, string) \
    field(scalar, uint8_t, SECP256K1_CMD_BYTES) \
    field(cfg, size_t) \
    field(trigger, size_t)
UJSON_SERDE_STRUCT(CryptoLibScaSECP256K1BaseMulIn, cryptolib_sca_secp256k1_base_mul_in_t, CRYPTOLIBSCA_SECP256K1_BASE_MUL_IN);

#define CRYPTOLIBSCA_SECP256K1_BASE_MUL_OUT(field, string) \
    field(x, uint8_t, SECP256K1_CMD_BYTES) \
    field(y, uint8_t, SECP256K1_CMD_BYTES) \
    field(cfg, size_t)
UJSON_SERDE_STRUCT(CryptoLibScaSECP256K1BaseMulOut, cryptolib_sca_secp256k1_base_mul_out_t, CRYPTOLIBSCA_SECP256K1_BASE_MUL_OUT);

#define CRYPTOLIBSCA_SECP256K1_POINT_MUL_IN(field, string) \
    field(scalar_alice, uint8_t, SECP256K1_CMD_BYTES) \
    field(scalar_bob, uint8_t, SECP256K1_CMD_BYTES) \
    field(cfg, size_t) \
    field(trigger, size_t)
UJSON_SERDE_STRUCT(CryptoLibScaSECP256K1PointMulIn, cryptolib_sca_secp256k1_point_mul_in_t, CRYPTOLIBSCA_SECP256K1_POINT_MUL_IN);

#define CRYPTOLIBSCA_SECP256K1_POINT_MUL_OUT(field, string) \
    field(x, uint8_t, SECP256K1_CMD_BYTES) \
    field(y, uint8_t, SECP256K1_CMD_BYTES) \
    field(cfg, size_t)
UJSON_SERDE_STRUCT(CryptoLibScaSECP256K1PointMulOut, cryptolib_sca_secp256k1_point_mul_out_t, CRYPTOLIBSCA_SECP256K1_POINT_MUL_OUT);

#define CRYPTOLIBSCA_SECP256K1_SIGN_IN(field, string) \
    field(scalar, uint8_t, SECP256K1_CMD_BYTES) \
    field(message, uint8_t, SECP256K1_CMD_BYTES) \
    field(cfg, size_t) \
    field(trigger, size_t)
UJSON_SERDE_STRUCT(CryptoLibScaSECP256K1SignIn, cryptolib_sca_secp256k1_sign_in_t, CRYPTOLIBSCA_SECP256K1_SIGN_IN);

#define CRYPTOLIBSCA_SECP256K1_SIGN_OUT(field, string) \
    field(r, uint8_t, SECP256K1_CMD_BYTES) \
    field(s, uint8_t, SECP256K1_CMD_BYTES) \
    field(pubx, uint8_t, SECP256K1_CMD_BYTES) \
    field(puby, uint8_t, SECP256K1_CMD_BYTES) \
    field(cfg, size_t)
UJSON_SERDE_STRUCT(CryptoLibScaSECP256K1SignOut, cryptolib_sca_secp256k1_sign_out_t, CRYPTOLIBSCA_SECP256K1_SIGN_OUT);

#define CRYPTOLIBSCA_X25519_BASE_MUL_IN(field, string) \
    field(scalar, uint8_t, X25519_CMD_BYTES) \
    field(cfg, size_t) \
    field(trigger, size_t)
UJSON_SERDE_STRUCT(CryptoLibScaX25519BaseMulIn, cryptolib_sca_x25519_base_mul_in_t, CRYPTOLIBSCA_X25519_BASE_MUL_IN);

#define CRYPTOLIBSCA_X25519_BASE_MUL_OUT(field, string) \
    field(x, uint8_t, X25519_CMD_BYTES) \
    field(y, uint8_t, X25519_CMD_BYTES) \
    field(cfg, size_t)
UJSON_SERDE_STRUCT(CryptoLibScaX25519BaseMulOut, cryptolib_sca_x25519_base_mul_out_t, CRYPTOLIBSCA_X25519_BASE_MUL_OUT);

#define CRYPTOLIBSCA_X25519_POINT_MUL_IN(field, string) \
    field(scalar_alice, uint8_t, X25519_CMD_BYTES) \
    field(scalar_bob, uint8_t, X25519_CMD_BYTES) \
    field(cfg, size_t) \
    field(trigger, size_t)
UJSON_SERDE_STRUCT(CryptoLibScaX25519PointMulIn, cryptolib_sca_x25519_point_mul_in_t, CRYPTOLIBSCA_X25519_POINT_MUL_IN);

#define CRYPTOLIBSCA_X25519_POINT_MUL_OUT(field, string) \
    field(x, uint8_t, X25519_CMD_BYTES) \
    field(y, uint8_t, X25519_CMD_BYTES) \
    field(cfg, size_t)
UJSON_SERDE_STRUCT(CryptoLibScaX25519PointMulOut, cryptolib_sca_x25519_point_mul_out_t, CRYPTOLIBSCA_X25519_POINT_MUL_OUT);

#define CRYPTOLIBSCA_ED25519_BASE_MUL_IN(field, string) \
    field(scalar, uint8_t, ED25519_CMD_SCALAR_BYTES) \
    field(cfg, size_t) \
    field(trigger, size_t)
UJSON_SERDE_STRUCT(CryptoLibScaED25519BaseMulIn, cryptolib_sca_ed25519_base_mul_in_t, CRYPTOLIBSCA_ED25519_BASE_MUL_IN);

#define CRYPTOLIBSCA_ED25519_BASE_MUL_OUT(field, string) \
    field(x, uint8_t, ED25519_CMD_SCALAR_BYTES) \
    field(y, uint8_t, ED25519_CMD_SCALAR_BYTES) \
    field(cfg, size_t)
UJSON_SERDE_STRUCT(CryptoLibScaED25519BaseMulOut, cryptolib_sca_ed25519_base_mul_out_t, CRYPTOLIBSCA_ED25519_BASE_MUL_OUT);

#define CRYPTOLIBSCA_ED25519_SIGN_IN(field, string) \
    field(scalar, uint8_t, ED25519_CMD_SCALAR_BYTES) \
    field(message, uint8_t, ED25519_CMD_MAX_MSG_BYTES) \
    field(message_len, size_t) \
    field(cfg, size_t) \
    field(trigger, size_t)
UJSON_SERDE_STRUCT(CryptoLibScaED25519SignIn, cryptolib_sca_ed25519_sign_in_t, CRYPTOLIBSCA_ED25519_SIGN_IN);

#define CRYPTOLIBSCA_ED25519_SIGN_OUT(field, string) \
    field(r, uint8_t, ED25519_CMD_SIG_BYTES) \
    field(s, uint8_t, ED25519_CMD_SIG_BYTES) \
    field(pubx, uint8_t, ED25519_CMD_SCALAR_BYTES) \
    field(puby, uint8_t, ED25519_CMD_SCALAR_BYTES) \
    field(cfg, size_t)
UJSON_SERDE_STRUCT(CryptoLibScaED25519SignOut, cryptolib_sca_ed25519_sign_out_t, CRYPTOLIBSCA_ED25519_SIGN_OUT);

// clang-format on

#ifdef __cplusplus
}
#endif
#endif  // OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_JSON_CRYPTOLIB_SCA_COMMANDS_H_
