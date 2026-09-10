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

#define MLDSA87_CMD_SEED_BYTES 32
#define MLDSA87_CMD_PUBLIC_KEY_BYTES 2592
#define MLDSA87_CMD_SIGNATURE_BYTES 4628
#define MLDSA87_CMD_MAX_MSG_BYTES 128
#define MLDSA87_CMD_MAX_CTX_BYTES 256

#define MLKEM1024_CMD_SEED_BYTES 32
#define MLKEM1024_CMD_PUBLIC_KEY_BYTES 1568
#define MLKEM1024_CMD_CIPHERTEXT_BYTES 1568
#define MLKEM1024_CMD_SHARED_SECRET_BYTES 32

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
    value(_, Mldsa87Keygen) \
    value(_, Mldsa87Sign) \
    value(_, Mldsa87Verify) \
    value(_, Mlkem1024Keygen) \
    value(_, Mlkem1024Encaps) \
    value(_, Mlkem1024Decaps) \
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

#define CRYPTOLIBSCAASYM_MLDSA87_KEYGEN_IN(field, string) \
    field(seed, uint8_t, MLDSA87_CMD_SEED_BYTES) \
    field(cfg, size_t) \
    field(trigger, size_t)
UJSON_SERDE_STRUCT(CryptoLibScaAsymMldsa87KeygenIn, cryptolib_sca_asym_mldsa87_keygen_in_t, CRYPTOLIBSCAASYM_MLDSA87_KEYGEN_IN);

#define CRYPTOLIBSCAASYM_MLDSA87_KEYGEN_OUT(field, string) \
    field(public_key, uint8_t, MLDSA87_CMD_PUBLIC_KEY_BYTES) \
    field(status, size_t) \
    field(cfg, size_t)
UJSON_SERDE_STRUCT(CryptoLibScaAsymMldsa87KeygenOut, cryptolib_sca_asym_mldsa87_keygen_out_t, CRYPTOLIBSCAASYM_MLDSA87_KEYGEN_OUT);

#define CRYPTOLIBSCAASYM_MLDSA87_SIGN_IN(field, string) \
    field(seed, uint8_t, MLDSA87_CMD_SEED_BYTES) \
    field(message, uint8_t, MLDSA87_CMD_MAX_MSG_BYTES) \
    field(message_len, size_t) \
    field(context, uint8_t, MLDSA87_CMD_MAX_CTX_BYTES) \
    field(context_len, size_t) \
    field(sign_mode, size_t) \
    field(cfg, size_t) \
    field(trigger, size_t)
UJSON_SERDE_STRUCT(CryptoLibScaAsymMldsa87SignIn, cryptolib_sca_asym_mldsa87_sign_in_t, CRYPTOLIBSCAASYM_MLDSA87_SIGN_IN);

#define CRYPTOLIBSCAASYM_MLDSA87_SIGN_OUT(field, string) \
    field(signature, uint8_t, MLDSA87_CMD_SIGNATURE_BYTES) \
    field(public_key, uint8_t, MLDSA87_CMD_PUBLIC_KEY_BYTES) \
    field(status, size_t) \
    field(cfg, size_t)
UJSON_SERDE_STRUCT(CryptoLibScaAsymMldsa87SignOut, cryptolib_sca_asym_mldsa87_sign_out_t, CRYPTOLIBSCAASYM_MLDSA87_SIGN_OUT);

#define CRYPTOLIBSCAASYM_MLDSA87_VERIFY_IN(field, string) \
    field(public_key, uint8_t, MLDSA87_CMD_PUBLIC_KEY_BYTES) \
    field(message, uint8_t, MLDSA87_CMD_MAX_MSG_BYTES) \
    field(message_len, size_t) \
    field(context, uint8_t, MLDSA87_CMD_MAX_CTX_BYTES) \
    field(context_len, size_t) \
    field(signature, uint8_t, MLDSA87_CMD_SIGNATURE_BYTES) \
    field(cfg, size_t) \
    field(trigger, size_t)
UJSON_SERDE_STRUCT(CryptoLibScaAsymMldsa87VerifyIn, cryptolib_sca_asym_mldsa87_verify_in_t, CRYPTOLIBSCAASYM_MLDSA87_VERIFY_IN);

#define CRYPTOLIBSCAASYM_MLDSA87_VERIFY_OUT(field, string) \
    field(result, bool) \
    field(status, size_t) \
    field(cfg, size_t)
UJSON_SERDE_STRUCT(CryptoLibScaAsymMldsa87VerifyOut, cryptolib_sca_asym_mldsa87_verify_out_t, CRYPTOLIBSCAASYM_MLDSA87_VERIFY_OUT);

#define CRYPTOLIBSCAASYM_MLKEM1024_KEYGEN_IN(field, string) \
    field(seed, uint8_t, MLKEM1024_CMD_SEED_BYTES) \
    field(cfg, size_t) \
    field(trigger, size_t)
UJSON_SERDE_STRUCT(CryptoLibScaAsymMlkem1024KeygenIn, cryptolib_sca_asym_mlkem1024_keygen_in_t, CRYPTOLIBSCAASYM_MLKEM1024_KEYGEN_IN);

#define CRYPTOLIBSCAASYM_MLKEM1024_KEYGEN_OUT(field, string) \
    field(public_key, uint8_t, MLKEM1024_CMD_PUBLIC_KEY_BYTES) \
    field(status, size_t) \
    field(cfg, size_t)
UJSON_SERDE_STRUCT(CryptoLibScaAsymMlkem1024KeygenOut, cryptolib_sca_asym_mlkem1024_keygen_out_t, CRYPTOLIBSCAASYM_MLKEM1024_KEYGEN_OUT);

#define CRYPTOLIBSCAASYM_MLKEM1024_ENCAPS_IN(field, string) \
    field(public_key, uint8_t, MLKEM1024_CMD_PUBLIC_KEY_BYTES) \
    field(m, uint8_t, MLKEM1024_CMD_SEED_BYTES) \
    field(cfg, size_t) \
    field(trigger, size_t)
UJSON_SERDE_STRUCT(CryptoLibScaAsymMlkem1024EncapsIn, cryptolib_sca_asym_mlkem1024_encaps_in_t, CRYPTOLIBSCAASYM_MLKEM1024_ENCAPS_IN);

#define CRYPTOLIBSCAASYM_MLKEM1024_ENCAPS_OUT(field, string) \
    field(ciphertext, uint8_t, MLKEM1024_CMD_CIPHERTEXT_BYTES) \
    field(shared_secret, uint8_t, MLKEM1024_CMD_SHARED_SECRET_BYTES) \
    field(status, size_t) \
    field(cfg, size_t)
UJSON_SERDE_STRUCT(CryptoLibScaAsymMlkem1024EncapsOut, cryptolib_sca_asym_mlkem1024_encaps_out_t, CRYPTOLIBSCAASYM_MLKEM1024_ENCAPS_OUT);

#define CRYPTOLIBSCAASYM_MLKEM1024_DECAPS_IN(field, string) \
    field(ciphertext, uint8_t, MLKEM1024_CMD_CIPHERTEXT_BYTES) \
    field(cfg, size_t) \
    field(trigger, size_t)
UJSON_SERDE_STRUCT(CryptoLibScaAsymMlkem1024DecapsIn, cryptolib_sca_asym_mlkem1024_decaps_in_t, CRYPTOLIBSCAASYM_MLKEM1024_DECAPS_IN);

#define CRYPTOLIBSCAASYM_MLKEM1024_DECAPS_OUT(field, string) \
    field(shared_secret, uint8_t, MLKEM1024_CMD_SHARED_SECRET_BYTES) \
    field(status, size_t) \
    field(cfg, size_t)
UJSON_SERDE_STRUCT(CryptoLibScaAsymMlkem1024DecapsOut, cryptolib_sca_asym_mlkem1024_decaps_out_t, CRYPTOLIBSCAASYM_MLKEM1024_DECAPS_OUT);

#undef MODULE_ID

// clang-format on

#ifdef __cplusplus
}
#endif
#endif  // OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_JSON_CRYPTOLIB_SCA_ASYM_COMMANDS_H_
