// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_RSA_RSA_DATATYPES_H_
#define OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_RSA_RSA_DATATYPES_H_

#include <stddef.h>
#include <stdint.h>

#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/crypto/impl/status.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

enum {
  /* Length of the RSA-2048 modulus and private exponent in bits. */
  kRsa2048NumBits = 2048,
  /* Length of the RSA-2048 modulus in bytes */
  kRsa2048NumBytes = kRsa2048NumBits / 8,
  /* Length of the RSA-2048 modulus in words */
  kRsa2048NumWords = kRsa2048NumBytes / sizeof(uint32_t),
  /* Length of the RSA-3072 modulus and private exponent in bits. */
  kRsa3072NumBits = 3072,
  /* Length of the RSA-3072 modulus in bytes */
  kRsa3072NumBytes = kRsa3072NumBits / 8,
  /* Length of the RSA-3072 modulus in words */
  kRsa3072NumWords = kRsa3072NumBytes / sizeof(uint32_t),
  /* Length of the RSA-4096 modulus and private exponent in bits. */
  kRsa4096NumBits = 4096,
  /* Length of the RSA-4096 modulus in bytes */
  kRsa4096NumBytes = kRsa4096NumBits / 8,
  /* Length of the RSA-4096 modulus in words */
  kRsa4096NumWords = kRsa4096NumBytes / sizeof(uint32_t),
};

/**
 * A type that holds a 2048-bit number.
 *
 * This type can be used for RSA-2048 signatures, moduli, private exponents,
 * and intermediate values.
 */
typedef struct rsa_2048_int_t {
  uint32_t data[kRsa2048NumWords];
} rsa_2048_int_t;

/**
 * A type that holds a 3072-bit number.
 *
 * This type can be used for RSA-3072 signatures, moduli, private exponents,
 * and intermediate values.
 */
typedef struct rsa_3072_int_t {
  uint32_t data[kRsa3072NumWords];
} rsa_3072_int_t;

/**
 * A type that holds a 4096-bit number.
 *
 * This type can be used for RSA-4096 signatures, moduli, private exponents,
 * and intermediate values.
 */
typedef struct rsa_4096_int_t {
  uint32_t data[kRsa4096NumWords];
} rsa_4096_int_t;

/**
 * A type that holds an RSA-2048 public key.
 *
 * The public key consists of a 2048-bit modulus n and a public exponent e.
 */
typedef struct rsa_2048_public_key_t {
  rsa_2048_int_t n;
  uint32_t e;
} rsa_2048_public_key_t;

/**
 * A type that holds an RSA-3072 public key.
 *
 * The public key consists of a 3072-bit modulus n and a public exponent e.
 */
typedef struct rsa_3072_public_key_t {
  rsa_3072_int_t n;
  uint32_t e;
} rsa_3072_public_key_t;

/**
 * A type that holds an RSA-4096 public key.
 *
 * The public key consists of a 4096-bit modulus n and a public exponent e.
 */
typedef struct rsa_4096_public_key_t {
  rsa_4096_int_t n;
  uint32_t e;
} rsa_4096_public_key_t;

/**
 * A type that holds an RSA-2048 private key.
 *
 * The private key consists of a 2048-bit private exponent d and a public
 * modulus n.
 */
typedef struct rsa_2048_private_key_t {
  rsa_2048_int_t d;
  rsa_2048_int_t n;
} rsa_2048_private_key_t;

/**
 * A type that holds an RSA-3072 private key.
 *
 * The private key consists of a 3072-bit private exponent d and a public
 * modulus n.
 */
typedef struct rsa_3072_private_key_t {
  rsa_3072_int_t d;
  rsa_3072_int_t n;
} rsa_3072_private_key_t;

/**
 * A type that holds an RSA-4096 private key.
 *
 * The private key consists of a 4096-bit private exponent d and a public
 * modulus n.
 */
typedef struct rsa_4096_private_key_t {
  rsa_4096_int_t d;
  rsa_4096_int_t n;
} rsa_4096_private_key_t;

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_RSA_RSA_DATATYPES_H_
