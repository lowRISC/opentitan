// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_JSON_CRYPTOLIB_FI_COMMANDS_H_
#define OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_JSON_CRYPTOLIB_FI_COMMANDS_H_
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

#define CRYPTOLIBFI_SUBCOMMAND(_, value) \
    value(_, Aes) \
    value(_, Cmac) \
    value(_, Gcm) \
    value(_, Tdes) \
    value(_, Hmac) \
    value(_, Drbg) \
    value(_, RsaEnc) \
    value(_, RsaSign) \
    value(_, Prime) \
    value(_, P256BaseMul) \
    value(_, P256PointMul) \
    value(_, P256Sign) \
    value(_, P256Verify) \
    value(_, P384BaseMul) \
    value(_, P384PointMul) \
    value(_, P384Sign) \
    value(_, P384Verify) \
    value(_, Secp256k1BaseMul) \
    value(_, Secp256k1PointMul) \
    value(_, Secp256k1Sign) \
    value(_, Secp256k1Verify) \
    value(_, X25519BaseMul) \
    value(_, X25519PointMul) \
    value(_, Ed25519BaseMul) \
    value(_, Ed25519Sign) \
    value(_, Ed25519Verify) \
    value(_, Init)
C_ONLY(UJSON_SERDE_ENUM(CryptoLibFiSubcommand, cryptolib_fi_subcommand_t, CRYPTOLIBFI_SUBCOMMAND));
RUST_ONLY(UJSON_SERDE_ENUM(CryptoLibFiSubcommand, cryptolib_fi_subcommand_t, CRYPTOLIBFI_SUBCOMMAND, RUST_DEFAULT_DERIVE, strum::EnumString));

#define CRYPTOLIBFI_AES_IN(field, string) \
    field(data, uint8_t, AES_CMD_MAX_MSG_BYTES) \
    field(data_len, size_t) \
    field(key, uint8_t, AES_CMD_MAX_KEY_BYTES) \
    field(key_len, size_t) \
    field(iv, uint8_t, AES_CMD_MAX_BLOCK_BYTES) \
    field(padding, size_t) \
    field(mode, size_t) \
    field(op_enc, bool) \
    field(cfg, size_t) \
    field(trigger, size_t)
UJSON_SERDE_STRUCT(CryptoLibFiAesIn, cryptolib_fi_aes_in_t, CRYPTOLIBFI_AES_IN);

#define CRYPTOLIBFI_AES_OUT(field, string) \
    field(data, uint8_t, AES_CMD_MAX_MSG_BYTES) \
    field(data_len, size_t) \
    field(cfg, size_t)
UJSON_SERDE_STRUCT(CryptoLibFiAesOut, cryptolib_fi_aes_out_t, CRYPTOLIBFI_AES_OUT);

#define CRYPTOLIBFI_CMAC_IN(field, string) \
    field(data, uint8_t, AES_CMD_MAX_MSG_BYTES) \
    field(data_len, size_t) \
    field(key, uint8_t, AES_CMD_MAX_KEY_BYTES) \
    field(key_len, size_t) \
    field(iv, uint8_t, AES_CMD_MAX_BLOCK_BYTES) \
    field(cfg, size_t) \
    field(trigger, size_t)
UJSON_SERDE_STRUCT(CryptoLibFiCmacIn, cryptolib_fi_cmac_in_t, CRYPTOLIBFI_CMAC_IN);

#define CRYPTOLIBFI_CMAC_OUT(field, string) \
    field(data, uint8_t, AES_CMD_MAX_MSG_BYTES) \
    field(data_len, size_t) \
    field(cfg, size_t)
UJSON_SERDE_STRUCT(CryptoLibFiCmacOut, cryptolib_fi_cmac_out_t, CRYPTOLIBFI_CMAC_OUT);

#define CRYPTOLIBFI_GCM_IN(field, string) \
    field(data, uint8_t, AES_CMD_MAX_MSG_BYTES) \
    field(data_len, size_t) \
    field(aad, uint8_t, AES_CMD_MAX_MSG_BYTES) \
    field(aad_len, size_t) \
    field(key, uint8_t, AES_CMD_MAX_KEY_BYTES) \
    field(key_len, size_t) \
    field(tag, uint8_t, AES_CMD_MAX_MSG_BYTES) \
    field(tag_len, uint32_t) \
    field(iv, uint8_t, AES_CMD_MAX_BLOCK_BYTES) \
    field(cfg, size_t) \
    field(trigger, size_t)
UJSON_SERDE_STRUCT(CryptoLibFiGcmIn, cryptolib_fi_gcm_in_t, CRYPTOLIBFI_GCM_IN);

#define CRYPTOLIBFI_GCM_OUT(field, string) \
    field(data, uint8_t, AES_CMD_MAX_MSG_BYTES) \
    field(data_len, uint32_t) \
    field(tag, uint8_t, AES_CMD_MAX_MSG_BYTES) \
    field(tag_len, uint32_t) \
    field(cfg, size_t)
UJSON_SERDE_STRUCT(CryptoLibFiGcmOut, cryptolib_fi_gcm_out_t, CRYPTOLIBFI_GCM_OUT);

#define CRYPTOLIBFI_TDES_IN(field, string) \
    field(data, uint8_t, TDES_CMD_MAX_MSG_BYTES) \
    field(data_len, size_t) \
    field(key, uint8_t, TDES_CMD_MAX_KEY_BYTES) \
    field(key_len, size_t) \
    field(iv, uint8_t, TDES_CMD_MAX_BLOCK_BYTES) \
    field(padding, size_t) \
    field(mode, size_t) \
    field(op_enc, bool) \
    field(cfg, size_t) \
    field(trigger, size_t)
UJSON_SERDE_STRUCT(CryptoLibFiTdesIn, cryptolib_fi_tdes_in_t, CRYPTOLIBFI_TDES_IN);

#define CRYPTOLIBFI_TDES_OUT(field, string) \
    field(data, uint8_t, TDES_CMD_MAX_MSG_BYTES) \
    field(data_len, size_t) \
    field(cfg, size_t)
UJSON_SERDE_STRUCT(CryptoLibFiTdesOut, cryptolib_fi_tdes_out_t, CRYPTOLIBFI_TDES_OUT);

#define CRYPTOLIBFI_HMAC_IN(field, string) \
    field(data, uint8_t, HMAC_CMD_MAX_MSG_BYTES) \
    field(data_len, size_t) \
    field(key, uint8_t, HMAC_CMD_MAX_KEY_BYTES) \
    field(key_len, size_t) \
    field(padding, size_t) \
    field(mode, size_t) \
    field(cfg, size_t) \
    field(trigger, size_t)
UJSON_SERDE_STRUCT(CryptoLibFiHmacIn, cryptolib_fi_hmac_in_t, CRYPTOLIBFI_HMAC_IN);

#define CRYPTOLIBFI_HMAC_OUT(field, string) \
    field(data, uint8_t, HMAC_CMD_MAX_TAG_BYTES) \
    field(data_len, size_t) \
    field(cfg, size_t)
UJSON_SERDE_STRUCT(CryptoLibFiHmacOut, cryptolib_fi_hmac_out_t, CRYPTOLIBFI_HMAC_OUT);

#define CRYPTOLIBFI_DRBG_IN(field, string) \
    field(entropy, uint8_t, DRBG_CMD_MAX_ENTROPY_BYTES) \
    field(entropy_len, size_t) \
    field(nonce, uint8_t, DRBG_CMD_MAX_NONCE_BYTES) \
    field(nonce_len, size_t) \
    field(reseed_interval, size_t) \
    field(mode, size_t) \
    field(cfg, size_t) \
    field(trigger, size_t)
UJSON_SERDE_STRUCT(CryptoLibFiDrbgIn, cryptolib_fi_drbg_in_t, CRYPTOLIBFI_DRBG_IN);

#define CRYPTOLIBFI_DRBG_OUT(field, string) \
    field(data, uint8_t, DRBG_CMD_MAX_OUTPUT_BYTES) \
    field(data_len, size_t) \
    field(cfg, size_t)
UJSON_SERDE_STRUCT(CryptoLibFiDrbgOut, cryptolib_fi_drbg_out_t, CRYPTOLIBFI_DRBG_OUT);

#define CRYPTOLIBFI_RSA_ENC_IN(field, string) \
    field(data, uint8_t, RSA_CMD_MAX_MESSAGE_BYTES) \
    field(data_len, size_t) \
    field(e, uint32_t) \
    field(n, uint8_t, RSA_CMD_MAX_N_BYTES) \
    field(d, uint8_t, RSA_CMD_MAX_N_BYTES) \
    field(n_len, size_t) \
    field(hashing, size_t) \
    field(padding, size_t) \
    field(op_enc, bool) \
    field(cfg, size_t) \
    field(trigger, size_t)
UJSON_SERDE_STRUCT(CryptoLibFiRsaEncIn, cryptolib_fi_rsa_enc_in_t, CRYPTOLIBFI_RSA_ENC_IN);

#define CRYPTOLIBFI_RSA_ENC_OUT(field, string) \
    field(n, uint8_t, RSA_CMD_MAX_N_BYTES) \
    field(d, uint8_t, RSA_CMD_MAX_N_BYTES) \
    field(n_len, size_t) \
    field(data, uint8_t, RSA_CMD_MAX_MESSAGE_BYTES) \
    field(data_len, size_t) \
    field(cfg, size_t)
UJSON_SERDE_STRUCT(CryptoLibFiRsaEncOut, cryptolib_fi_rsa_enc_out_t, CRYPTOLIBFI_RSA_ENC_OUT);

#define CRYPTOLIBFI_RSA_SIGN_IN(field, string) \
    field(data, uint8_t, RSA_CMD_MAX_MESSAGE_BYTES) \
    field(data_len, size_t) \
    field(e, uint32_t) \
    field(n, uint8_t, RSA_CMD_MAX_N_BYTES) \
    field(d, uint8_t, RSA_CMD_MAX_N_BYTES) \
    field(n_len, size_t) \
    field(sig, uint8_t, RSA_CMD_MAX_SIGNATURE_BYTES) \
    field(sig_len, size_t) \
    field(hashing, size_t) \
    field(padding, size_t) \
    field(cfg, size_t) \
    field(trigger, size_t)
UJSON_SERDE_STRUCT(CryptoLibFiRsaSignIn, cryptolib_fi_rsa_sign_in_t, CRYPTOLIBFI_RSA_SIGN_IN);

#define CRYPTOLIBFI_RSA_SIGN_OUT(field, string) \
    field(n, uint8_t, RSA_CMD_MAX_N_BYTES) \
    field(d, uint8_t, RSA_CMD_MAX_N_BYTES) \
    field(n_len, size_t) \
    field(sig, uint8_t, RSA_CMD_MAX_SIGNATURE_BYTES) \
    field(sig_len, size_t) \
    field(cfg, size_t)
UJSON_SERDE_STRUCT(CryptoLibFiRsaSignOut, cryptolib_fi_rsa_sign_out_t, CRYPTOLIBFI_RSA_SIGN_OUT);

#define CRYPTOLIBFI_PRIME_IN(field, string) \
    field(e, uint32_t) \
    field(cfg, size_t) \
    field(trigger, size_t)
UJSON_SERDE_STRUCT(CryptoLibFiPrimeIn, cryptolib_fi_prime_in_t, CRYPTOLIBFI_PRIME_IN);

#define CRYPTOLIBFI_PRIME_OUT(field, string) \
    field(prime, uint8_t, RSA_CMD_MAX_N_BYTES) \
    field(prime_len, size_t) \
    field(cfg, size_t)
UJSON_SERDE_STRUCT(CryptoLibFiPrimeOut, cryptolib_fi_prime_out_t, CRYPTOLIBFI_PRIME_OUT);

#define CRYPTOLIBFI_P256_BASE_MUL_IN(field, string) \
    field(scalar, uint8_t, P256_CMD_BYTES) \
    field(cfg, size_t) \
    field(trigger, size_t)
UJSON_SERDE_STRUCT(CryptoLibFiP256BaseMulIn, cryptolib_fi_p256_base_mul_in_t, CRYPTOLIBFI_P256_BASE_MUL_IN);

#define CRYPTOLIBFI_P256_BASE_MUL_OUT(field, string) \
    field(x, uint8_t, P256_CMD_BYTES) \
    field(y, uint8_t, P256_CMD_BYTES) \
    field(cfg, size_t)
UJSON_SERDE_STRUCT(CryptoLibFiP256BaseMulOut, cryptolib_fi_p256_base_mul_out_t, CRYPTOLIBFI_P256_BASE_MUL_OUT);

#define CRYPTOLIBFI_P256_POINT_MUL_IN(field, string) \
    field(scalar_alice, uint8_t, P256_CMD_BYTES) \
    field(scalar_bob, uint8_t, P256_CMD_BYTES) \
    field(cfg, size_t) \
    field(trigger, size_t)
UJSON_SERDE_STRUCT(CryptoLibFiP256PointMulIn, cryptolib_fi_p256_point_mul_in_t, CRYPTOLIBFI_P256_POINT_MUL_IN);

#define CRYPTOLIBFI_P256_POINT_MUL_OUT(field, string) \
    field(x, uint8_t, P256_CMD_BYTES) \
    field(y, uint8_t, P256_CMD_BYTES) \
    field(cfg, size_t)
UJSON_SERDE_STRUCT(CryptoLibFiP256PointMulOut, cryptolib_fi_p256_point_mul_out_t, CRYPTOLIBFI_P256_POINT_MUL_OUT);

#define CRYPTOLIBFI_P256_SIGN_IN(field, string) \
    field(scalar, uint8_t, P256_CMD_BYTES) \
    field(message, uint8_t, P256_CMD_BYTES) \
    field(cfg, size_t) \
    field(trigger, size_t)
UJSON_SERDE_STRUCT(CryptoLibFiP256SignIn, cryptolib_fi_p256_sign_in_t, CRYPTOLIBFI_P256_SIGN_IN);

#define CRYPTOLIBFI_P256_SIGN_OUT(field, string) \
    field(r, uint8_t, P256_CMD_BYTES) \
    field(s, uint8_t, P256_CMD_BYTES) \
    field(pubx, uint8_t, P256_CMD_BYTES) \
    field(puby, uint8_t, P256_CMD_BYTES) \
    field(cfg, size_t)
UJSON_SERDE_STRUCT(CryptoLibFiP256SignOut, cryptolib_fi_p256_sign_out_t, CRYPTOLIBFI_P256_SIGN_OUT);

#define CRYPTOLIBFI_P256_VERIFY_IN(field, string) \
    field(pubx, uint8_t, P256_CMD_BYTES) \
    field(puby, uint8_t, P256_CMD_BYTES) \
    field(r, uint8_t, P256_CMD_BYTES) \
    field(s, uint8_t, P256_CMD_BYTES) \
    field(message, uint8_t, P256_CMD_BYTES) \
    field(cfg, size_t) \
    field(trigger, size_t)
UJSON_SERDE_STRUCT(CryptoLibFiP256VerifyIn, cryptolib_fi_p256_verify_in_t, CRYPTOLIBFI_P256_VERIFY_IN);

#define CRYPTOLIBFI_P256_VERIFY_OUT(field, string) \
    field(result, bool) \
    field(cfg, size_t)
UJSON_SERDE_STRUCT(CryptoLibFiP256VerifyOut, cryptolib_fi_p256_verify_out_t, CRYPTOLIBFI_P256_VERIFY_OUT);

#define CRYPTOLIBFI_P384_BASE_MUL_IN(field, string) \
    field(scalar, uint8_t, P384_CMD_BYTES) \
    field(cfg, size_t) \
    field(trigger, size_t)
UJSON_SERDE_STRUCT(CryptoLibFiP384BaseMulIn, cryptolib_fi_p384_base_mul_in_t, CRYPTOLIBFI_P384_BASE_MUL_IN);

#define CRYPTOLIBFI_P384_BASE_MUL_OUT(field, string) \
    field(x, uint8_t, P384_CMD_BYTES) \
    field(y, uint8_t, P384_CMD_BYTES) \
    field(cfg, size_t)
UJSON_SERDE_STRUCT(CryptoLibFiP384BaseMulOut, cryptolib_fi_p384_base_mul_out_t, CRYPTOLIBFI_P384_BASE_MUL_OUT);

#define CRYPTOLIBFI_P384_POINT_MUL_IN(field, string) \
    field(scalar_alice, uint8_t, P384_CMD_BYTES) \
    field(scalar_bob, uint8_t, P384_CMD_BYTES) \
    field(cfg, size_t) \
    field(trigger, size_t)
UJSON_SERDE_STRUCT(CryptoLibFiP384PointMulIn, cryptolib_fi_p384_point_mul_in_t, CRYPTOLIBFI_P384_POINT_MUL_IN);

#define CRYPTOLIBFI_P384_POINT_MUL_OUT(field, string) \
    field(x, uint8_t, P384_CMD_BYTES) \
    field(y, uint8_t, P384_CMD_BYTES) \
    field(cfg, size_t)
UJSON_SERDE_STRUCT(CryptoLibFiP384PointMulOut, cryptolib_fi_p384_point_mul_out_t, CRYPTOLIBFI_P384_POINT_MUL_OUT);

#define CRYPTOLIBFI_P384_SIGN_IN(field, string) \
    field(scalar, uint8_t, P384_CMD_BYTES) \
    field(message, uint8_t, P384_CMD_BYTES) \
    field(cfg, size_t) \
    field(trigger, size_t)
UJSON_SERDE_STRUCT(CryptoLibFiP384SignIn, cryptolib_fi_p384_sign_in_t, CRYPTOLIBFI_P384_SIGN_IN);

#define CRYPTOLIBFI_P384_SIGN_OUT(field, string) \
    field(r, uint8_t, P384_CMD_BYTES) \
    field(s, uint8_t, P384_CMD_BYTES) \
    field(pubx, uint8_t, P384_CMD_BYTES) \
    field(puby, uint8_t, P384_CMD_BYTES) \
    field(cfg, size_t)
UJSON_SERDE_STRUCT(CryptoLibFiP384SignOut, cryptolib_fi_p384_sign_out_t, CRYPTOLIBFI_P384_SIGN_OUT);

#define CRYPTOLIBFI_P384_VERIFY_IN(field, string) \
    field(pubx, uint8_t, P384_CMD_BYTES) \
    field(puby, uint8_t, P384_CMD_BYTES) \
    field(r, uint8_t, P384_CMD_BYTES) \
    field(s, uint8_t, P384_CMD_BYTES) \
    field(message, uint8_t, P384_CMD_BYTES) \
    field(cfg, size_t) \
    field(trigger, size_t)
UJSON_SERDE_STRUCT(CryptoLibFiP384VerifyIn, cryptolib_fi_p384_verify_in_t, CRYPTOLIBFI_P384_VERIFY_IN);

#define CRYPTOLIBFI_P384_VERIFY_OUT(field, string) \
    field(result, bool) \
    field(cfg, size_t)
UJSON_SERDE_STRUCT(CryptoLibFiP384VerifyOut, cryptolib_fi_p384_verify_out_t, CRYPTOLIBFI_P384_VERIFY_OUT);

#define CRYPTOLIBFI_SECP256K1_BASE_MUL_IN(field, string) \
    field(scalar, uint8_t, SECP256K1_CMD_BYTES) \
    field(cfg, size_t) \
    field(trigger, size_t)
UJSON_SERDE_STRUCT(CryptoLibFiSECP256K1BaseMulIn, cryptolib_fi_secp256k1_base_mul_in_t, CRYPTOLIBFI_SECP256K1_BASE_MUL_IN);

#define CRYPTOLIBFI_SECP256K1_BASE_MUL_OUT(field, string) \
    field(x, uint8_t, SECP256K1_CMD_BYTES) \
    field(y, uint8_t, SECP256K1_CMD_BYTES) \
    field(cfg, size_t)
UJSON_SERDE_STRUCT(CryptoLibFiSECP256K1BaseMulOut, cryptolib_fi_secp256k1_base_mul_out_t, CRYPTOLIBFI_SECP256K1_BASE_MUL_OUT);

#define CRYPTOLIBFI_SECP256K1_POINT_MUL_IN(field, string) \
    field(scalar_alice, uint8_t, SECP256K1_CMD_BYTES) \
    field(scalar_bob, uint8_t, SECP256K1_CMD_BYTES) \
    field(cfg, size_t) \
    field(trigger, size_t)
UJSON_SERDE_STRUCT(CryptoLibFiSECP256K1PointMulIn, cryptolib_fi_secp256k1_point_mul_in_t, CRYPTOLIBFI_SECP256K1_POINT_MUL_IN);

#define CRYPTOLIBFI_SECP256K1_POINT_MUL_OUT(field, string) \
    field(x, uint8_t, SECP256K1_CMD_BYTES) \
    field(y, uint8_t, SECP256K1_CMD_BYTES) \
    field(cfg, size_t)
UJSON_SERDE_STRUCT(CryptoLibFiSECP256K1PointMulOut, cryptolib_fi_secp256k1_point_mul_out_t, CRYPTOLIBFI_SECP256K1_POINT_MUL_OUT);

#define CRYPTOLIBFI_SECP256K1_SIGN_IN(field, string) \
    field(scalar, uint8_t, SECP256K1_CMD_BYTES) \
    field(message, uint8_t, SECP256K1_CMD_BYTES) \
    field(cfg, size_t) \
    field(trigger, size_t)
UJSON_SERDE_STRUCT(CryptoLibFiSECP256K1SignIn, cryptolib_fi_secp256k1_sign_in_t, CRYPTOLIBFI_SECP256K1_SIGN_IN);

#define CRYPTOLIBFI_SECP256K1_SIGN_OUT(field, string) \
    field(r, uint8_t, SECP256K1_CMD_BYTES) \
    field(s, uint8_t, SECP256K1_CMD_BYTES) \
    field(pubx, uint8_t, SECP256K1_CMD_BYTES) \
    field(puby, uint8_t, SECP256K1_CMD_BYTES) \
    field(cfg, size_t)
UJSON_SERDE_STRUCT(CryptoLibFiSECP256K1SignOut, cryptolib_fi_secp256k1_sign_out_t, CRYPTOLIBFI_SECP256K1_SIGN_OUT);

#define CRYPTOLIBFI_SECP256K1_VERIFY_IN(field, string) \
    field(pubx, uint8_t, SECP256K1_CMD_BYTES) \
    field(puby, uint8_t, SECP256K1_CMD_BYTES) \
    field(r, uint8_t, SECP256K1_CMD_BYTES) \
    field(s, uint8_t, SECP256K1_CMD_BYTES) \
    field(message, uint8_t, SECP256K1_CMD_BYTES) \
    field(cfg, size_t) \
    field(trigger, size_t)
UJSON_SERDE_STRUCT(CryptoLibFiSECP256K1VerifyIn, cryptolib_fi_secp256k1_verify_in_t, CRYPTOLIBFI_SECP256K1_VERIFY_IN);

#define CRYPTOLIBFI_SECP256K1_VERIFY_OUT(field, string) \
    field(result, bool) \
    field(cfg, size_t)
UJSON_SERDE_STRUCT(CryptoLibFiSECP256K1VerifyOut, cryptolib_fi_secp256k1_verify_out_t, CRYPTOLIBFI_SECP256K1_VERIFY_OUT);

#define CRYPTOLIBFI_X25519_BASE_MUL_IN(field, string) \
    field(scalar, uint8_t, X25519_CMD_BYTES) \
    field(cfg, size_t) \
    field(trigger, size_t)
UJSON_SERDE_STRUCT(CryptoLibFiX25519BaseMulIn, cryptolib_fi_x25519_base_mul_in_t, CRYPTOLIBFI_X25519_BASE_MUL_IN);

#define CRYPTOLIBFI_X25519_BASE_MUL_OUT(field, string) \
    field(x, uint8_t, X25519_CMD_BYTES) \
    field(y, uint8_t, X25519_CMD_BYTES) \
    field(cfg, size_t)
UJSON_SERDE_STRUCT(CryptoLibFiX25519BaseMulOut, cryptolib_fi_x25519_base_mul_out_t, CRYPTOLIBFI_X25519_BASE_MUL_OUT);

#define CRYPTOLIBFI_X25519_POINT_MUL_IN(field, string) \
    field(scalar_alice, uint8_t, X25519_CMD_BYTES) \
    field(scalar_bob, uint8_t, X25519_CMD_BYTES) \
    field(cfg, size_t) \
    field(trigger, size_t)
UJSON_SERDE_STRUCT(CryptoLibFiX25519PointMulIn, cryptolib_fi_x25519_point_mul_in_t, CRYPTOLIBFI_X25519_POINT_MUL_IN);

#define CRYPTOLIBFI_X25519_POINT_MUL_OUT(field, string) \
    field(x, uint8_t, X25519_CMD_BYTES) \
    field(y, uint8_t, X25519_CMD_BYTES) \
    field(cfg, size_t)
UJSON_SERDE_STRUCT(CryptoLibFiX25519PointMulOut, cryptolib_fi_x25519_point_mul_out_t, CRYPTOLIBFI_X25519_POINT_MUL_OUT);

#define CRYPTOLIBFI_ED25519_BASE_MUL_IN(field, string) \
    field(scalar, uint8_t, ED25519_CMD_SCALAR_BYTES) \
    field(cfg, size_t) \
    field(trigger, size_t)
UJSON_SERDE_STRUCT(CryptoLibFiED25519BaseMulIn, cryptolib_fi_ed25519_base_mul_in_t, CRYPTOLIBFI_ED25519_BASE_MUL_IN);

#define CRYPTOLIBFI_ED25519_BASE_MUL_OUT(field, string) \
    field(x, uint8_t, ED25519_CMD_SCALAR_BYTES) \
    field(y, uint8_t, ED25519_CMD_SCALAR_BYTES) \
    field(cfg, size_t)
UJSON_SERDE_STRUCT(CryptoLibFiED25519BaseMulOut, cryptolib_fi_ed25519_base_mul_out_t, CRYPTOLIBFI_ED25519_BASE_MUL_OUT);

#define CRYPTOLIBFI_ED25519_SIGN_IN(field, string) \
    field(scalar, uint8_t, ED25519_CMD_SCALAR_BYTES) \
    field(message, uint8_t, ED25519_CMD_MAX_MSG_BYTES) \
    field(message_len, size_t) \
    field(cfg, size_t) \
    field(trigger, size_t)
UJSON_SERDE_STRUCT(CryptoLibFiED25519SignIn, cryptolib_fi_ed25519_sign_in_t, CRYPTOLIBFI_ED25519_SIGN_IN);

#define CRYPTOLIBFI_ED25519_SIGN_OUT(field, string) \
    field(r, uint8_t, ED25519_CMD_SIG_BYTES) \
    field(s, uint8_t, ED25519_CMD_SIG_BYTES) \
    field(pubx, uint8_t, ED25519_CMD_SCALAR_BYTES) \
    field(puby, uint8_t, ED25519_CMD_SCALAR_BYTES) \
    field(cfg, size_t)
UJSON_SERDE_STRUCT(CryptoLibFiED25519SignOut, cryptolib_fi_ed25519_sign_out_t, CRYPTOLIBFI_ED25519_SIGN_OUT);

#define CRYPTOLIBFI_ED25519_VERIFY_IN(field, string) \
    field(pubx, uint8_t, ED25519_CMD_SCALAR_BYTES) \
    field(puby, uint8_t, ED25519_CMD_SCALAR_BYTES) \
    field(r, uint8_t, ED25519_CMD_SIG_BYTES) \
    field(s, uint8_t, ED25519_CMD_SIG_BYTES) \
    field(message, uint8_t, ED25519_CMD_MAX_MSG_BYTES) \
    field(message_len, size_t) \
    field(cfg, size_t) \
    field(trigger, size_t)
UJSON_SERDE_STRUCT(CryptoLibFiED25519VerifyIn, cryptolib_fi_ed25519_verify_in_t, CRYPTOLIBFI_ED25519_VERIFY_IN);

#define CRYPTOLIBFI_ED25519_VERIFY_OUT(field, string) \
    field(result, bool) \
    field(cfg, size_t)
UJSON_SERDE_STRUCT(CryptoLibFiED25519VerifyOut, cryptolib_fi_ed25519_verify_out_t, CRYPTOLIBFI_ED25519_VERIFY_OUT);

// clang-format on

#ifdef __cplusplus
}
#endif
#endif  // OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_JSON_CRYPTOLIB_FI_COMMANDS_H_
