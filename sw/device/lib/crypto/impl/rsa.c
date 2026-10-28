// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/include/rsa.h"

#include <stdbool.h>

#include "sw/device/lib/base/crc32.h"
#include "sw/device/lib/base/hardened_memory.h"
#include "sw/device/lib/base/math.h"
#include "sw/device/lib/crypto/drivers/otbn.h"
#include "sw/device/lib/crypto/impl/cmvp.h"
#include "sw/device/lib/crypto/impl/hash.h"
#include "sw/device/lib/crypto/impl/rsa/rsa_encryption.h"
#include "sw/device/lib/crypto/impl/rsa/rsa_signature.h"
#include "sw/device/lib/crypto/impl/rsa/run_rsa.h"
#include "sw/device/lib/crypto/impl/rsa/run_rsa_key_from_cofactor.h"
#include "sw/device/lib/crypto/impl/state.h"
#include "sw/device/lib/crypto/impl/status.h"
#include "sw/device/lib/crypto/include/config.h"
#include "sw/device/lib/crypto/include/datatypes.h"
#include "sw/device/lib/crypto/include/integrity.h"

// Module ID for status codes.
#define MODULE_ID MAKE_MODULE_ID('r', 's', 'a')

static_assert(kOtcryptoRsa2048PublicKeyBytes == sizeof(rsa_2048_public_key_t),
              "RSA-2048 public key size mismatch.");
static_assert(kOtcryptoRsa3072PublicKeyBytes == sizeof(rsa_3072_public_key_t),
              "RSA-3072 public key size mismatch.");
static_assert(kOtcryptoRsa4096PublicKeyBytes == sizeof(rsa_4096_public_key_t),
              "RSA-4096 public key size mismatch.");
static_assert(kOtcryptoRsa2048PrivateKeyBytes == sizeof(rsa_2048_int_t),
              "RSA-2048 private key size mismatch.");
static_assert(kOtcryptoRsa3072PrivateKeyBytes == sizeof(rsa_3072_int_t),
              "RSA-3072 private key size mismatch.");
static_assert(kOtcryptoRsa4096PrivateKeyBytes == sizeof(rsa_4096_int_t),
              "RSA-4096 private key size mismatch.");
static_assert(kOtcryptoRsa2048PrivateKeyblobBytes ==
                  sizeof(rsa_2048_private_key_t),
              "RSA-2048 keyblob size mismatch.");
static_assert(kOtcryptoRsa3072PrivateKeyblobBytes ==
                  sizeof(rsa_3072_private_key_t),
              "RSA-3072 keyblob size mismatch.");
static_assert(kOtcryptoRsa4096PrivateKeyblobBytes ==
                  sizeof(rsa_4096_private_key_t),
              "RSA-4096 keyblob size mismatch.");
static_assert(kOtcryptoWrappedKeyMaxWords ==
                  sizeof(otcrypto_key_config_t) / sizeof(uint32_t) + 2 +
                      kOtcryptoRsa4096PrivateKeyblobBytes / sizeof(uint32_t) +
                      1 + 2,
              "kOtcryptoWrappedKeyMaxWords does not match wrapped RSA-4096 "
              "private key size.");
static_assert(offsetof(rsa_2048_private_key_t, d0) == 0 &&
                  offsetof(rsa_2048_private_key_t, d1) ==
                      kRsa2048NumWords * sizeof(uint32_t) &&
                  offsetof(rsa_2048_private_key_t, n) ==
                      2 * kRsa2048NumWords * sizeof(uint32_t) &&
                  offsetof(rsa_2048_private_key_t, checksum) ==
                      3 * kRsa2048NumWords * sizeof(uint32_t),
              "RSA-2048 private key layout mismatch.");
static_assert(offsetof(rsa_3072_private_key_t, d0) == 0 &&
                  offsetof(rsa_3072_private_key_t, d1) ==
                      kRsa3072NumWords * sizeof(uint32_t) &&
                  offsetof(rsa_3072_private_key_t, n) ==
                      2 * kRsa3072NumWords * sizeof(uint32_t) &&
                  offsetof(rsa_3072_private_key_t, checksum) ==
                      3 * kRsa3072NumWords * sizeof(uint32_t),
              "RSA-3072 private key layout mismatch.");
static_assert(offsetof(rsa_4096_private_key_t, d0) == 0 &&
                  offsetof(rsa_4096_private_key_t, d1) ==
                      kRsa4096NumWords * sizeof(uint32_t) &&
                  offsetof(rsa_4096_private_key_t, n) ==
                      2 * kRsa4096NumWords * sizeof(uint32_t) &&
                  offsetof(rsa_4096_private_key_t, checksum) ==
                      3 * kRsa4096NumWords * sizeof(uint32_t),
              "RSA-4096 private key layout mismatch.");

/**
 * Convert a top-level `otcrypto_rsa_size_t` to the internal `rsa_size_t` and
 * modulus word length.
 *
 * @param size Top-level RSA size parameter.
 * @param[out] rsa_size Internal RSA size parameter (optional, may be NULL).
 * @param[out] num_words Modulus length in 32-bit words.
 * @return OK if `size` is valid, OTCRYPTO_BAD_ARGS otherwise.
 */
static status_t rsa_size_to_params(otcrypto_rsa_size_t size,
                                   rsa_size_t *rsa_size, size_t *num_words) {
  *num_words = 0;
  rsa_size_t local_size = (rsa_size_t)0;
  switch (launder32(size)) {
    case kOtcryptoRsaSize2048:
      HARDENED_CHECK_EQ(size, kOtcryptoRsaSize2048);
      local_size = kRsaSize2048;
      *num_words = kRsa2048NumWords;
      break;
    case kOtcryptoRsaSize3072:
      HARDENED_CHECK_EQ(size, kOtcryptoRsaSize3072);
      local_size = kRsaSize3072;
      *num_words = kRsa3072NumWords;
      break;
    case kOtcryptoRsaSize4096:
      HARDENED_CHECK_EQ(size, kOtcryptoRsaSize4096);
      local_size = kRsaSize4096;
      *num_words = kRsa4096NumWords;
      break;
    default:
      return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_NE(*num_words, 0);
  if (rsa_size != NULL) {
    *rsa_size = local_size;
  }
  return OTCRYPTO_OK;
}

/**
 * Convert a word length to the internal `rsa_size_t`.
 *
 * @param num_words Modulus/signature/ciphertext length in 32-bit words.
 * @param[out] rsa_size Internal RSA size parameter.
 * @return OK if `num_words` is valid, OTCRYPTO_BAD_ARGS otherwise.
 */
static status_t rsa_size_from_num_words(size_t num_words,
                                        rsa_size_t *rsa_size) {
  *rsa_size = (rsa_size_t)0;
  switch (launder32(num_words)) {
    case kRsa2048NumWords:
      HARDENED_CHECK_EQ(num_words, kRsa2048NumWords);
      *rsa_size = kRsaSize2048;
      return OTCRYPTO_OK;
    case kRsa3072NumWords:
      HARDENED_CHECK_EQ(num_words, kRsa3072NumWords);
      *rsa_size = kRsaSize3072;
      return OTCRYPTO_OK;
    case kRsa4096NumWords:
      HARDENED_CHECK_EQ(num_words, kRsa4096NumWords);
      *rsa_size = kRsaSize4096;
      return OTCRYPTO_OK;
    default:
      return OTCRYPTO_BAD_ARGS;
  }

  // Should be unreachable.
  HARDENED_TRAP();
  // COVERAGE (FI CM) Unreachable code, checked against fault injections.
  return OTCRYPTO_FATAL_ERR;
}

static inline bool is_even(uint32_t v) { return (v & 1) == 0; }

/**
 * Check if a key mode is intended for RSA.
 *
 * @param mode Mode to check.
 * @return OK if the mode is for RSA, OTCRYPTO_BAD_ARGS otherwise.
 */
static status_t rsa_mode_check(const otcrypto_key_mode_t mode) {
  switch (launder32(mode)) {
    case kOtcryptoKeyModeRsaSignPkcs:
      HARDENED_CHECK_EQ(mode, kOtcryptoKeyModeRsaSignPkcs);
      return OTCRYPTO_OK;
    case kOtcryptoKeyModeRsaSignPss:
      HARDENED_CHECK_EQ(mode, kOtcryptoKeyModeRsaSignPss);
      return OTCRYPTO_OK;
    case kOtcryptoKeyModeRsaEncryptOaep:
      HARDENED_CHECK_EQ(mode, kOtcryptoKeyModeRsaEncryptOaep);
      return OTCRYPTO_OK;
    default:
      return OTCRYPTO_BAD_ARGS;
  }

  // Should be unreachable.
  HARDENED_TRAP();
  // COVERAGE (FI CM) Unreachable code, checked against fault injections.
  return OTCRYPTO_FATAL_ERR;
}

/**
 * Compute a less-than check (a < b) on two bignums of equal number of words.
 * This function runs in constant time.
 *
 * @param a First operand.
 * @param b Second operand.
 * @param num_words Number of 32-bit words in both operands (> 0).
 * @return True if a < b.
 */
static hardened_bool_t bignum_lt(const uint32_t *a, const uint32_t *b,
                                 size_t num_words) {
  HARDENED_CHECK_NE(num_words, 0);

  size_t i = num_words;
  ct_bool32_t is_lt = 0;
  ct_bool32_t is_gt = 0;
  do {
    i--;
    is_lt = is_lt | (!is_gt && (a[i] < b[i]));
    is_gt = is_gt | (!is_lt && (a[i] > b[i]));
  } while (i != 0);
  HARDENED_CHECK_EQ(i, 0);

  return is_lt && !is_gt ? kHardenedBoolTrue : kHardenedBoolFalse;
}

otcrypto_status_t otcrypto_rsa_public_key_construct(
    otcrypto_rsa_size_t size, const otcrypto_const_word32_buf_t *modulus,
    otcrypto_unblinded_key_t *public_key) {
  OTCRYPTO_LOCKED_STATE_CHECK();
#ifndef OTCRYPTO_DISABLE_NULL_CHECKS
  if (modulus == NULL || modulus->data == NULL || public_key == NULL ||
      public_key->key == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }
#endif
  HARDENED_TRY(rsa_mode_check(public_key->key_mode));

  if (is_even(modulus->data[0])) {
    return OTCRYPTO_BAD_ARGS;
  }

  size_t num_words = 0;
  HARDENED_TRY(rsa_size_to_params(size, NULL, &num_words));
  if (public_key->key_length != num_words * sizeof(uint32_t) ||
      modulus->len != num_words) {
    // COVERAGE (MISSING) We do not cover bad key lengths.
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(public_key->key_length, num_words * sizeof(uint32_t));
  HARDENED_CHECK_EQ(modulus->len, num_words);
  HARDENED_TRY(hardened_memcpy(public_key->key, modulus->data, num_words));

  // Verify the input buffer
  HARDENED_CHECK_EQ(kHardenedBoolTrue, OTCRYPTO_CHECK_BUF(modulus));

  public_key->checksum = otcrypto_integrity_unblinded_checksum(public_key);
  return otcrypto_eval_exit(OTCRYPTO_OK);
}

/**
 * Basic structural validity checks for RSA private key buffers.
 *
 * Checks for bad length, invalid key modes, or an unsupported configuration.
 * Does not verify checksums or actual key data requirements because this
 * routine is used for keygen as well as other operations, when the key data is
 * not yet populated.
 *
 * @param size RSA size parameter.
 * @param private_key Key to check.
 * @return OK if the key is valid, OTCRYPTO_BAD_ARGS otherwise.
 */
static status_t private_key_structural_check(
    const otcrypto_rsa_size_t size, const otcrypto_blinded_key_t *private_key) {
  // Check that the key mode is a valid RSA mode.
  HARDENED_TRY(rsa_mode_check(private_key->config.key_mode));

  // Sideloaded keys are not supported for RSA.
  if (private_key->config.hw_backed != kHardenedBoolFalse) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Check the lengths against the RSA size.
  size_t num_words = 0;
  HARDENED_TRY(rsa_size_to_params(size, NULL, &num_words));
  size_t key_length = num_words * sizeof(uint32_t);
  size_t keyblob_length = (3 * num_words + 1) * sizeof(uint32_t);
  HARDENED_CHECK_NE(key_length, 0);
  HARDENED_CHECK_NE(keyblob_length, 0);

  if (private_key->config.key_length != key_length ||
      private_key->keyblob_length != keyblob_length) {
    return OTCRYPTO_BAD_ARGS;
  }

  return OTCRYPTO_OK;
}

/**
 * Infer the RSA key size from the byte length of a public or private key.
 *
 * @param key_bytelen Key length in bytes.
 * @param[out] key_size RSA key size.
 * @return OK if the key length is valid, OTCRYPTO_BAD_ARGS otherwise.
 */
static status_t rsa_size_from_key_bytelen(size_t key_bytelen,
                                          otcrypto_rsa_size_t *key_size) {
  switch (launder32(key_bytelen)) {
    case kOtcryptoRsa2048PublicKeyBytes:
      HARDENED_CHECK_EQ(key_bytelen, kOtcryptoRsa2048PublicKeyBytes);
      *key_size = kOtcryptoRsaSize2048;
      return OTCRYPTO_OK;
    case kOtcryptoRsa3072PublicKeyBytes:
      HARDENED_CHECK_EQ(key_bytelen, kOtcryptoRsa3072PublicKeyBytes);
      *key_size = kOtcryptoRsaSize3072;
      return OTCRYPTO_OK;
    case kOtcryptoRsa4096PublicKeyBytes:
      HARDENED_CHECK_EQ(key_bytelen, kOtcryptoRsa4096PublicKeyBytes);
      *key_size = kOtcryptoRsaSize4096;
      return OTCRYPTO_OK;
    default:
      // No matches.
      return OTCRYPTO_BAD_ARGS;
  }

  // Should be unreachable.
  HARDENED_TRAP();
  // COVERAGE (FI CM) Unreachable code, checked against fault injections.
  return OTCRYPTO_FATAL_ERR;
}

/**
 * Infer the RSA key size from the length of the public key.
 *
 * @param public_key Public key.
 * @param[out] key_size RSA key size.
 * @return OK if the key is valid, OTCRYPTO_BAD_ARGS otherwise.
 */
static status_t rsa_size_from_public_key(
    const otcrypto_unblinded_key_t *public_key, otcrypto_rsa_size_t *key_size) {
  return rsa_size_from_key_bytelen(public_key->key_length, key_size);
}

/**
 * Infer the RSA key size from the length of the private key.
 *
 * @param private_key Private key.
 * @param[out] key_size RSA key size.
 * @return OK if the key is valid, OTCRYPTO_BAD_ARGS otherwise.
 */
static status_t rsa_size_from_private_key(
    const otcrypto_blinded_key_t *private_key, otcrypto_rsa_size_t *key_size) {
  return rsa_size_from_key_bytelen(private_key->config.key_length, key_size);
}

/**
 * Basic structural validity checks for RSA public key buffers.
 *
 * Checks for NULL pointers or invalid key modes. Does not verify checksums
 * or actual key data requirements because this routine is used for keygen as
 * well as other operations, when the key data is not yet populated.
 *
 * @param public_key Key to check.
 * @return OK if the key is valid, OTCRYPTO_BAD_ARGS otherwise.
 */
static status_t public_key_structural_check(
    const otcrypto_unblinded_key_t *public_key) {
  // Check that the key mode is a valid RSA mode.
  return rsa_mode_check(public_key->key_mode);
}

otcrypto_status_t otcrypto_rsa_keygen_async_start(otcrypto_rsa_size_t size) {
  OTCRYPTO_SET_CMVP_INDICATOR(OTCRYPTO_FUNCTION_RSA_KEYGEN_ASYNC_START);
  OTCRYPTO_HEALTH_CHECK(kTestRsa4096SignBit);
  OTCRYPTO_HEALTH_CHECK(size == kOtcryptoRsaSize2048 ? kTestRsa2048VerifyBit
                                                     : kTestRsa4096VerifyBit);
  if (size == kOtcryptoRsaSize2048) {
    OTCRYPTO_CMVP_OVERRIDE_NOT_APPROVED();
  }
  rsa_size_t rsa_size = (rsa_size_t)0;
  size_t num_words = 0;
  HARDENED_TRY(rsa_size_to_params(size, &rsa_size, &num_words));
  HARDENED_TRY(rsa_keygen_start(rsa_size));
  return otcrypto_eval_exit(OTCRYPTO_OK);
}

otcrypto_status_t otcrypto_rsa_keygen(otcrypto_rsa_size_t size,
                                      otcrypto_unblinded_key_t *public_key,
                                      otcrypto_blinded_key_t *private_key) {
  OTCRYPTO_LOCKED_STATE_CHECK();
#ifndef OTCRYPTO_DISABLE_NULL_CHECKS
  if (public_key == NULL || private_key == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }
#endif
  // Check the size against the public key.
  otcrypto_rsa_size_t inferred_size;
  if (!status_ok(rsa_size_from_public_key(public_key, &inferred_size)) ||
      inferred_size != size) {
    return OTCRYPTO_BAD_ARGS;
  }

  HARDENED_TRY(otcrypto_rsa_keygen_async_start(size));
  return otcrypto_rsa_keygen_async_finalize(public_key, private_key);
}

otcrypto_status_t otcrypto_rsa_prime_check(
    otcrypto_rsa_size_t size,
    const otcrypto_const_word32_buf_t *prime_candidate,
    hardened_bool_t *prime_ok) {
  OTCRYPTO_SET_CMVP_INDICATOR(OTCRYPTO_FUNCTION_RSA_PRIME_CHECK);
  OTCRYPTO_LOCKED_STATE_CHECK();
#ifndef OTCRYPTO_DISABLE_NULL_CHECKS
  if (prime_candidate == NULL || prime_candidate->data == NULL ||
      prime_ok == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }
#endif
  *prime_ok = kHardenedBoolFalse;
  HARDENED_CHECK_EQ(kHardenedBoolTrue, OTCRYPTO_CHECK_BUF(prime_candidate));

  rsa_size_t rsa_size = (rsa_size_t)0;
  size_t num_words = 0;
  HARDENED_TRY(rsa_size_to_params(size, &rsa_size, &num_words));
  size_t prime_words = num_words / 2;
  if (prime_candidate->len != prime_words) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(prime_candidate->len, prime_words);

  // The OTBN Miller-Rabin routine requires p = 3 (mod 4) and the MSB set.
  if ((prime_candidate->data[0] & 3) != 3 ||
      (prime_candidate->data[prime_words - 1] >> 31) == 0) {
    return OTCRYPTO_BAD_ARGS;
  }

  HARDENED_TRY_WIPE_DMEM(
      rsa_prime_check(rsa_size, prime_candidate->data, prime_ok));
  return otcrypto_eval_exit(OTCRYPTO_OK);
}

otcrypto_status_t otcrypto_rsa_create_n_from_primes(
    otcrypto_rsa_size_t size, const otcrypto_const_word32_buf_t *prime_p,
    const otcrypto_const_word32_buf_t *prime_q,
    otcrypto_word32_buf_t *modulus) {
  OTCRYPTO_SET_CMVP_INDICATOR(OTCRYPTO_FUNCTION_RSA_CREATE_N_FROM_PRIMES);
  OTCRYPTO_LOCKED_STATE_CHECK();
#ifndef OTCRYPTO_DISABLE_NULL_CHECKS
  if (prime_p == NULL || prime_p->data == NULL || prime_q == NULL ||
      prime_q->data == NULL || modulus == NULL || modulus->data == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }
#endif
  HARDENED_CHECK_EQ(kHardenedBoolTrue, OTCRYPTO_CHECK_BUF(prime_p));
  HARDENED_CHECK_EQ(kHardenedBoolTrue, OTCRYPTO_CHECK_BUF(prime_q));
  HARDENED_CHECK_EQ(kHardenedBoolTrue, OTCRYPTO_CHECK_BUF(modulus));

  rsa_size_t rsa_size = (rsa_size_t)0;
  size_t num_words = 0;
  HARDENED_TRY(rsa_size_to_params(size, &rsa_size, &num_words));
  size_t prime_words = num_words / 2;
  if (prime_p->len != prime_words || prime_q->len != prime_words ||
      modulus->len != num_words) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(prime_p->len, prime_words);
  HARDENED_CHECK_EQ(prime_q->len, prime_words);
  HARDENED_CHECK_EQ(modulus->len, num_words);

  if (is_even(prime_p->data[0]) || is_even(prime_q->data[0])) {
    return OTCRYPTO_BAD_ARGS;
  }

  HARDENED_TRY_WIPE_DMEM(rsa_create_n_from_primes(
      rsa_size, prime_p->data, prime_q->data, modulus->data));
  return otcrypto_eval_exit(OTCRYPTO_OK);
}

otcrypto_status_t otcrypto_rsa_private_key_from_exponents(
    otcrypto_rsa_size_t size, const otcrypto_const_word32_buf_t *modulus,
    const otcrypto_const_word32_buf_t *d_share0,
    const otcrypto_const_word32_buf_t *d_share1,
    otcrypto_blinded_key_t *private_key) {
  OTCRYPTO_LOCKED_STATE_CHECK();
#ifndef OTCRYPTO_DISABLE_NULL_CHECKS
  if (modulus == NULL || modulus->data == NULL || d_share0 == NULL ||
      d_share0->data == NULL || d_share1 == NULL || d_share1->data == NULL ||
      private_key == NULL || private_key->keyblob == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }
#endif
  HARDENED_TRY(rsa_mode_check(private_key->config.key_mode));

  // Ensure that the length of the private exponent shares matches the length
  // of the modulus.
  if (d_share0->len != modulus->len || d_share1->len != modulus->len) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Check the mode and lengths for the private key.
  HARDENED_TRY(private_key_structural_check(size, private_key));

  if (is_even(modulus->data[0])) {
    // COVERAGE (MISSING) We do not cover even moduli.
    return OTCRYPTO_BAD_ARGS;
  }

  // Randomize the keyblob.
  HARDENED_TRY(hardened_memshred(
      private_key->keyblob,
      ceil_div(private_key->keyblob_length, sizeof(uint32_t))));

  size_t num_words = 0;
  HARDENED_TRY(rsa_size_to_params(size, NULL, &num_words));
  if (private_key->keyblob_length != (3 * num_words + 1) * sizeof(uint32_t) ||
      modulus->len != num_words) {
    // COVERAGE (MISSING) We do not cover bad key lengths.
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(modulus->len, num_words);
  HARDENED_CHECK_EQ(d_share0->len, num_words);
  HARDENED_CHECK_EQ(d_share1->len, num_words);
  uint32_t *d0 = private_key->keyblob;
  uint32_t *d1 = &private_key->keyblob[num_words];
  uint32_t *n = &private_key->keyblob[2 * num_words];
  uint32_t *checksum = &private_key->keyblob[3 * num_words];
  HARDENED_TRY(hardened_memcpy(n, modulus->data, num_words));
  HARDENED_TRY(hardened_memcpy(d0, d_share0->data, num_words));
  HARDENED_TRY(hardened_memcpy(d1, d_share1->data, num_words));
  *checksum = crc32(d_share0->data, num_words * sizeof(uint32_t));

  // Verify the input buffers
  HARDENED_CHECK_EQ(kHardenedBoolTrue, OTCRYPTO_CHECK_BUF(modulus));
  HARDENED_CHECK_EQ(kHardenedBoolTrue, OTCRYPTO_CHECK_BUF(d_share0));

  private_key->checksum = otcrypto_integrity_blinded_checksum(private_key);
  return otcrypto_eval_exit(OTCRYPTO_OK);
}

otcrypto_status_t otcrypto_rsa_keypair_from_cofactor(
    otcrypto_rsa_size_t size, const otcrypto_const_word32_buf_t *modulus,
    const otcrypto_const_word32_buf_t *cofactor_share0,
    const otcrypto_const_word32_buf_t *cofactor_share1,
    otcrypto_unblinded_key_t *public_key, otcrypto_blinded_key_t *private_key) {
  OTCRYPTO_LOCKED_STATE_CHECK();
#ifndef OTCRYPTO_DISABLE_NULL_CHECKS
  if (public_key == NULL || private_key == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }
#endif
  // Check the size against the public key.
  otcrypto_rsa_size_t inferred_size;
  if (!status_ok(rsa_size_from_public_key(public_key, &inferred_size)) ||
      inferred_size != size) {
    return OTCRYPTO_BAD_ARGS;
  }

  HARDENED_TRY(otcrypto_rsa_keypair_from_cofactor_async_start(
      size, modulus, cofactor_share0, cofactor_share1));
  return otcrypto_rsa_keypair_from_cofactor_async_finalize(public_key,
                                                           private_key);
}

otcrypto_status_t otcrypto_rsa_sign(const otcrypto_blinded_key_t *private_key,
                                    const otcrypto_hash_digest_t message_digest,
                                    otcrypto_rsa_padding_t padding_mode,
                                    otcrypto_word32_buf_t *signature) {
  HARDENED_TRY(
      otcrypto_rsa_sign_async_start(private_key, message_digest, padding_mode));
  return otcrypto_rsa_sign_async_finalize(signature);
}

/**
 * Ensure that the key mode matches the RSA sign padding mode.
 *
 * Only works for RSA signing keys; do not use with encryption keys.
 *
 * @param key_mode Mode for the RSA key.
 * @param padding_mode RSA signature padding scheme.
 */
static status_t key_mode_padding_check(otcrypto_key_mode_t key_mode,
                                       otcrypto_rsa_padding_t padding_mode) {
  switch (launder32(padding_mode)) {
    case kOtcryptoRsaPaddingPkcs:
      HARDENED_CHECK_EQ(padding_mode, kOtcryptoRsaPaddingPkcs);
      if (launder32(key_mode) != kOtcryptoKeyModeRsaSignPkcs) {
        // COVERAGE (MISSING) We do not cover mismatching key_mode and
        // padding_modes.
        return OTCRYPTO_BAD_ARGS;
      }
      HARDENED_CHECK_EQ(key_mode, kOtcryptoKeyModeRsaSignPkcs);
      return OTCRYPTO_OK;
    case kOtcryptoRsaPaddingPss:
      HARDENED_CHECK_EQ(padding_mode, kOtcryptoRsaPaddingPss);
      if (launder32(key_mode) != kOtcryptoKeyModeRsaSignPss) {
        return OTCRYPTO_BAD_ARGS;
      }
      HARDENED_CHECK_EQ(key_mode, kOtcryptoKeyModeRsaSignPss);
      return OTCRYPTO_OK;
    default:
      // Invalid padding mode.
      return OTCRYPTO_BAD_ARGS;
  }

  // Should be unreachable.
  HARDENED_TRAP();
  // COVERAGE (FI CM) Unreachable code, checked against fault injections.
  return OTCRYPTO_FATAL_ERR;
}

otcrypto_status_t otcrypto_rsa_verify(
    const otcrypto_unblinded_key_t *public_key,
    const otcrypto_hash_digest_t message_digest,
    otcrypto_rsa_padding_t padding_mode,
    const otcrypto_const_word32_buf_t *signature,
    hardened_bool_t *verification_result) {
  HARDENED_TRY(otcrypto_rsa_verify_async_start(public_key, signature));
  HARDENED_TRY(key_mode_padding_check(public_key->key_mode, padding_mode));
  return otcrypto_rsa_verify_async_finalize(message_digest, padding_mode,
                                            verification_result);
}

otcrypto_status_t otcrypto_rsa_hash_sign_verify(
    const otcrypto_blinded_key_t *private_key,
    const otcrypto_unblinded_key_t *public_key, otcrypto_hash_mode_t hash_mode,
    const otcrypto_const_byte_buf_t *message,
    otcrypto_rsa_padding_t padding_mode, otcrypto_word32_buf_t *signature) {
  OTCRYPTO_SET_CMVP_INDICATOR(OTCRYPTO_FUNCTION_RSA_HASH_SIGN_VERIFY);
  OTCRYPTO_HEALTH_CHECK(kTestRsa4096SignBit);
  if (private_key != NULL &&
      private_key->config.key_length == kOtcryptoRsa2048PrivateKeyBytes) {
    OTCRYPTO_CMVP_OVERRIDE_NOT_APPROVED();
  }
  uint32_t digest_data[16];
  HARDENED_TRY(hardened_memshred(digest_data, ARRAYSIZE(digest_data)));
  otcrypto_hash_digest_t digest;
  HARDENED_TRY(hash_message(hash_mode, message, digest_data, &digest));
  HARDENED_TRY(otcrypto_rsa_sign(private_key, digest, padding_mode, signature));
  otcrypto_const_word32_buf_t signature_check = OTCRYPTO_MAKE_BUF(
      otcrypto_const_word32_buf_t, signature->data, signature->len);
  hardened_bool_t verification_result = kHardenedBoolFalse;
  HARDENED_TRY(otcrypto_rsa_verify(public_key, digest, padding_mode,
                                   &signature_check, &verification_result));
  HARDENED_TRY(hardened_memshred(digest_data, ARRAYSIZE(digest_data)));
  if (verification_result != kHardenedBoolTrue) {
    // COVERAGE (FI CM) This check only fails if the signature generation was
    // faulted.
    crypto_state_t *state = NULL;
    if (status_ok(read_state_pointer(&state)) && state != NULL) {
      state->locked_state = kHardenedByteBoolTrue;
    }
    return OTCRYPTO_FATAL_ERR;
  }
  HARDENED_CHECK_EQ(verification_result, kHardenedBoolTrue);
  return otcrypto_eval_exit(OTCRYPTO_OK);
}

otcrypto_status_t otcrypto_rsa_hash_verify(
    const otcrypto_unblinded_key_t *public_key, otcrypto_hash_mode_t hash_mode,
    const otcrypto_const_byte_buf_t *message,
    otcrypto_rsa_padding_t padding_mode,
    const otcrypto_const_word32_buf_t *signature,
    hardened_bool_t *verification_result) {
  OTCRYPTO_SET_CMVP_INDICATOR(OTCRYPTO_FUNCTION_RSA_HASH_VERIFY);
  OTCRYPTO_LOCKED_STATE_CHECK();
  uint32_t digest_data[16];
  HARDENED_TRY(hardened_memshred(digest_data, ARRAYSIZE(digest_data)));
  otcrypto_hash_digest_t digest;
  HARDENED_TRY(hash_message(hash_mode, message, digest_data, &digest));
  return otcrypto_eval_exit(otcrypto_rsa_verify(
      public_key, digest, padding_mode, signature, verification_result));
}

otcrypto_status_t otcrypto_rsa_encrypt(
    const otcrypto_unblinded_key_t *public_key,
    const otcrypto_hash_mode_t hash_mode,
    const otcrypto_const_byte_buf_t *message,
    const otcrypto_const_byte_buf_t *label, otcrypto_word32_buf_t *ciphertext) {
  HARDENED_TRY(
      otcrypto_rsa_encrypt_async_start(public_key, hash_mode, message, label));
  return otcrypto_rsa_encrypt_async_finalize(ciphertext);
}

otcrypto_status_t otcrypto_rsa_decrypt(
    const otcrypto_blinded_key_t *private_key,
    const otcrypto_hash_mode_t hash_mode,
    const otcrypto_const_word32_buf_t *ciphertext,
    const otcrypto_const_byte_buf_t *label, otcrypto_byte_buf_t *plaintext,
    size_t *plaintext_bytelen) {
  HARDENED_TRY(otcrypto_rsa_decrypt_async_start(private_key, ciphertext));
  return otcrypto_rsa_decrypt_async_finalize(hash_mode, label, plaintext,
                                             plaintext_bytelen);
}

#ifdef FIPS_MODE
/**
 * Perform Pairwise Consistency Test (PCT) for RSA key generation.
 * Signs a dummy message with the generated private key and verifies the
 * signature with the generated public key.
 */
static otcrypto_status_t rsa_pct_verify(
    otcrypto_rsa_size_t size, const otcrypto_unblinded_key_t *public_key,
    const otcrypto_blinded_key_t *private_key) {
  uint8_t dummy_msg_data[32] = {0};
  otcrypto_const_byte_buf_t msg = OTCRYPTO_MAKE_BUF(
      otcrypto_const_byte_buf_t, dummy_msg_data, sizeof(dummy_msg_data));

  uint32_t sig_data[128];
  size_t sig_words = 0;
  HARDENED_TRY(rsa_size_to_params(size, NULL, &sig_words));

  otcrypto_unblinded_key_t pct_public_key = *public_key;
  pct_public_key.key_mode = kOtcryptoKeyModeRsaSignPkcs;
  pct_public_key.checksum =
      otcrypto_integrity_unblinded_checksum(&pct_public_key);

  otcrypto_blinded_key_t pct_private_key = *private_key;
  pct_private_key.config.key_mode = kOtcryptoKeyModeRsaSignPkcs;
  pct_private_key.checksum =
      otcrypto_integrity_blinded_checksum(&pct_private_key);

  otcrypto_word32_buf_t sig = otcrypto_make_word32_buf(sig_data, sig_words);
  return otcrypto_rsa_hash_sign_verify(&pct_private_key, &pct_public_key,
                                       kOtcryptoHashModeSha512, &msg,
                                       kOtcryptoRsaPaddingPkcs, &sig);
}
#endif

otcrypto_status_t otcrypto_rsa_keygen_async_finalize(
    otcrypto_unblinded_key_t *public_key, otcrypto_blinded_key_t *private_key) {
  OTCRYPTO_SET_CMVP_INDICATOR(OTCRYPTO_FUNCTION_RSA_KEYGEN_ASYNC_FINALIZE);
  OTCRYPTO_LOCKED_STATE_CHECK();
#ifndef OTCRYPTO_DISABLE_NULL_CHECKS
  // Check for NULL pointers.
  if (public_key == NULL || public_key->key == NULL || private_key == NULL ||
      private_key->keyblob == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }
#endif

  // Infer the RSA size from the public key modulus.
  otcrypto_rsa_size_t size;
  HARDENED_TRY(rsa_size_from_public_key(public_key, &size));
  if (size == kOtcryptoRsaSize2048) {
    OTCRYPTO_CMVP_OVERRIDE_NOT_APPROVED();
  }

  // Check the caller-provided public key buffer.
  HARDENED_TRY(public_key_structural_check(public_key));

  // Check the caller-provided private key buffer.
  HARDENED_TRY(private_key_structural_check(size, private_key));

  // Randomize the keyblob memory.
  HARDENED_TRY(hardened_memshred(
      private_key->keyblob,
      ceil_div(private_key->keyblob_length, sizeof(uint32_t))));

  // Call the required finalize() operation.
  rsa_size_t rsa_size = (rsa_size_t)0;
  size_t num_words = 0;
  HARDENED_TRY(rsa_size_to_params(size, &rsa_size, &num_words));
  uint32_t *d0 = private_key->keyblob;
  uint32_t *d1 = &private_key->keyblob[num_words];
  uint32_t *n = &private_key->keyblob[2 * num_words];
  uint32_t *checksum = &private_key->keyblob[3 * num_words];
  HARDENED_TRY_WIPE_DMEM(
      rsa_keygen_finalize_size(rsa_size, n, d0, d1, NULL, NULL));
  HARDENED_TRY(hardened_memcpy(public_key->key, n, num_words));
  *checksum = crc32(d0, num_words * sizeof(uint32_t));

  // Construct checksums for the new keys.
  public_key->checksum = otcrypto_integrity_unblinded_checksum(public_key);
  private_key->checksum = otcrypto_integrity_blinded_checksum(private_key);

#ifdef FIPS_MODE
  // Perform FIPS Pairwise Consistency Test (PCT).
  HARDENED_TRY(rsa_pct_verify(size, public_key, private_key));
#endif

  return otcrypto_eval_exit(OTCRYPTO_OK);
}

otcrypto_status_t otcrypto_rsa_keypair_from_cofactor_async_start(
    otcrypto_rsa_size_t size, const otcrypto_const_word32_buf_t *modulus,
    const otcrypto_const_word32_buf_t *cofactor_share0,
    const otcrypto_const_word32_buf_t *cofactor_share1) {
  OTCRYPTO_SET_CMVP_INDICATOR(
      OTCRYPTO_FUNCTION_RSA_KEYPAIR_FROM_COFACTOR_ASYNC_START);
  OTCRYPTO_HEALTH_CHECK(kTestRsa4096SignBit);
  OTCRYPTO_HEALTH_CHECK(size == kOtcryptoRsaSize2048 ? kTestRsa2048VerifyBit
                                                     : kTestRsa4096VerifyBit);
#ifndef OTCRYPTO_DISABLE_NULL_CHECKS
  if (modulus == NULL || modulus->data == NULL || cofactor_share0 == NULL ||
      cofactor_share0->data == NULL || cofactor_share1 == NULL ||
      cofactor_share1->data == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }
#endif

  // Verify the input buffers
  HARDENED_CHECK_EQ(kHardenedBoolTrue, OTCRYPTO_CHECK_BUF(modulus));
  HARDENED_CHECK_EQ(kHardenedBoolTrue, OTCRYPTO_CHECK_BUF(cofactor_share0));

  // Ensure that the length of the cofactor shares is half the length
  // of the modulus.
  if (cofactor_share0->len != modulus->len / 2 ||
      cofactor_share1->len != modulus->len / 2) {
    return OTCRYPTO_BAD_ARGS;
  }

  if (is_even(modulus->data[0])) {
    return OTCRYPTO_BAD_ARGS;
  }

  rsa_size_t rsa_size = (rsa_size_t)0;
  size_t num_words = 0;
  HARDENED_TRY(rsa_size_to_params(size, &rsa_size, &num_words));
  if (cofactor_share0->len != num_words / 2 || modulus->len != num_words) {
    // COVERAGE (MISSING) We do not cover bad size.
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(modulus->len, num_words);
  HARDENED_CHECK_EQ(cofactor_share0->len, num_words / 2);
  HARDENED_CHECK_EQ(cofactor_share1->len, num_words / 2);
  HARDENED_TRY_WIPE_DMEM(rsa_keygen_from_cofactor_start(
      rsa_size, modulus->data, cofactor_share0->data, cofactor_share1->data));
  return otcrypto_eval_exit(OTCRYPTO_OK);
}

otcrypto_status_t otcrypto_rsa_keypair_from_cofactor_async_finalize(
    otcrypto_unblinded_key_t *public_key, otcrypto_blinded_key_t *private_key) {
  OTCRYPTO_SET_CMVP_INDICATOR(
      OTCRYPTO_FUNCTION_RSA_KEYPAIR_FROM_COFACTOR_ASYNC_FINALIZE);
  OTCRYPTO_LOCKED_STATE_CHECK();
#ifndef OTCRYPTO_DISABLE_NULL_CHECKS
  // Check for NULL pointers.
  if (public_key == NULL || public_key->key == NULL || private_key == NULL ||
      private_key->keyblob == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }
#endif

  // Infer the RSA size from the public key modulus.
  otcrypto_rsa_size_t size;
  HARDENED_TRY(rsa_size_from_public_key(public_key, &size));

  // Check the caller-provided public key buffer.
  HARDENED_TRY(public_key_structural_check(public_key));

  // Check the caller-provided private key buffer.
  HARDENED_TRY(private_key_structural_check(size, private_key));

  // Randomize the keyblob memory.
  HARDENED_TRY(hardened_memshred(
      private_key->keyblob,
      ceil_div(private_key->keyblob_length, sizeof(uint32_t))));

  // Call the required finalize() operation.
  rsa_size_t rsa_size = (rsa_size_t)0;
  size_t num_words = 0;
  HARDENED_TRY(rsa_size_to_params(size, &rsa_size, &num_words));
  uint32_t *d0 = private_key->keyblob;
  uint32_t *d1 = &private_key->keyblob[num_words];
  uint32_t *n = &private_key->keyblob[2 * num_words];
  uint32_t *checksum = &private_key->keyblob[3 * num_words];
  HARDENED_TRY_WIPE_DMEM(
      rsa_keygen_from_cofactor_finalize(rsa_size, public_key->key, n, d0, d1));
  *checksum = crc32(d0, num_words * sizeof(uint32_t));

  // Construct checksums for the new keys.
  public_key->checksum = otcrypto_integrity_unblinded_checksum(public_key);
  private_key->checksum = otcrypto_integrity_blinded_checksum(private_key);
  return otcrypto_eval_exit(OTCRYPTO_OK);
}

static otcrypto_status_t rsa_sign_exp_async_start(
    const otcrypto_blinded_key_t *private_key, uint32_t exponent,
    const otcrypto_hash_digest_t message_digest,
    otcrypto_rsa_padding_t padding_mode) {
  OTCRYPTO_SET_CMVP_INDICATOR(OTCRYPTO_FUNCTION_RSA_SIGN_ASYNC_START);
  OTCRYPTO_HEALTH_CHECK(kTestRsa4096SignBit);
#ifndef OTCRYPTO_DISABLE_NULL_CHECKS
  // Check for NULL pointers.
  if (message_digest.data == NULL || private_key == NULL ||
      private_key->keyblob == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }
#endif

  // Infer the RSA size from the private key.
  otcrypto_rsa_size_t size;
  HARDENED_TRY(rsa_size_from_private_key(private_key, &size));

  // Check the caller-provided private key buffer.
  HARDENED_TRY(private_key_structural_check(size, private_key));

  // Ensure the key mode matches the padding mode.
  HARDENED_TRY(
      key_mode_padding_check(private_key->config.key_mode, padding_mode));

  // Verify the checksum.
  if (otcrypto_integrity_blinded_key_check(private_key) != kHardenedBoolTrue) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Start the signature generation routine.
  rsa_size_t rsa_size = (rsa_size_t)0;
  size_t num_words = 0;
  HARDENED_TRY(rsa_size_to_params(size, &rsa_size, &num_words));
  const uint32_t *d0 = private_key->keyblob;
  const uint32_t *d1 = &private_key->keyblob[num_words];
  const uint32_t *n = &private_key->keyblob[2 * num_words];
  uint32_t checksum = private_key->keyblob[3 * num_words];
  HARDENED_TRY_WIPE_DMEM(rsa_signature_generate_start(
      rsa_size, d0, d1, exponent, n, checksum, message_digest,
      (rsa_signature_padding_t)padding_mode));
  return otcrypto_eval_exit(OTCRYPTO_OK);
}

otcrypto_status_t otcrypto_rsa_sign_async_start(
    const otcrypto_blinded_key_t *private_key,
    const otcrypto_hash_digest_t message_digest,
    otcrypto_rsa_padding_t padding_mode) {
  return rsa_sign_exp_async_start(private_key, /*exponent=*/0, message_digest,
                                  padding_mode);
}

otcrypto_status_t otcrypto_rsa_sign_async_finalize(
    otcrypto_word32_buf_t *signature) {
  OTCRYPTO_SET_CMVP_INDICATOR(OTCRYPTO_FUNCTION_RSA_SIGN_ASYNC_FINALIZE);
  OTCRYPTO_LOCKED_STATE_CHECK();
#ifndef OTCRYPTO_DISABLE_NULL_CHECKS
  // Check for NULL pointers.
  if (signature == NULL || signature->data == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }
#endif

  // Verify the input buffer
  HARDENED_CHECK_EQ(kHardenedBoolTrue, OTCRYPTO_CHECK_BUF(signature));

  // Determine the size based on the signature buffer length.
  rsa_size_t rsa_size = (rsa_size_t)0;
  HARDENED_TRY(rsa_size_from_num_words(signature->len, &rsa_size));
  HARDENED_TRY_WIPE_DMEM(
      rsa_signature_generate_finalize(rsa_size, signature->data));
  return otcrypto_eval_exit(OTCRYPTO_OK);
}

static otcrypto_status_t rsa_verify_exp_async_start(
    const otcrypto_unblinded_key_t *public_key, uint32_t exponent,
    const otcrypto_const_word32_buf_t *signature) {
  OTCRYPTO_SET_CMVP_INDICATOR(OTCRYPTO_FUNCTION_RSA_VERIFY_ASYNC_START);
  OTCRYPTO_LOCKED_STATE_CHECK();
#ifndef OTCRYPTO_DISABLE_NULL_CHECKS
  // Check for NULL pointers.
  if (public_key == NULL || public_key->key == NULL || signature == NULL ||
      signature->data == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }
#endif

  // Verify the input buffer
  HARDENED_CHECK_EQ(kHardenedBoolTrue, OTCRYPTO_CHECK_BUF(signature));

  // Check the caller-provided public key buffer.
  HARDENED_TRY(public_key_structural_check(public_key));
  if (launder32(public_key->key_mode) == kOtcryptoKeyModeRsaEncryptOaep) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Verify the checksum.
  if (otcrypto_integrity_unblinded_key_check(public_key) != kHardenedBoolTrue) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Infer the RSA size from the public key.
  otcrypto_rsa_size_t size;
  HARDENED_TRY(rsa_size_from_public_key(public_key, &size));
  OTCRYPTO_HEALTH_CHECK(size == kOtcryptoRsaSize2048 ? kTestRsa2048VerifyBit
                                                     : kTestRsa4096VerifyBit);

  rsa_size_t rsa_size = (rsa_size_t)0;
  size_t num_words = 0;
  HARDENED_TRY(rsa_size_to_params(size, &rsa_size, &num_words));
  if (signature->len != num_words) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(signature->len, num_words);
  // Check that signature is < n.
  if (bignum_lt(signature->data, public_key->key, num_words) ==
      kHardenedBoolFalse) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_TRY_WIPE_DMEM(rsa_signature_verify_start(
      rsa_size, exponent, public_key->key, signature->data));
  return otcrypto_eval_exit(OTCRYPTO_OK);
}

otcrypto_status_t otcrypto_rsa_verify_async_start(
    const otcrypto_unblinded_key_t *public_key,
    const otcrypto_const_word32_buf_t *signature) {
  return rsa_verify_exp_async_start(public_key, /*exponent=*/0, signature);
}

otcrypto_status_t otcrypto_rsa_verify_async_finalize(
    const otcrypto_hash_digest_t message_digest,
    otcrypto_rsa_padding_t padding_mode, hardened_bool_t *verification_result) {
  OTCRYPTO_SET_CMVP_INDICATOR(OTCRYPTO_FUNCTION_RSA_VERIFY_ASYNC_FINALIZE);
  OTCRYPTO_LOCKED_STATE_CHECK();
#ifndef OTCRYPTO_DISABLE_NULL_CHECKS
  // Check for NULL pointers.
  if (message_digest.data == NULL || verification_result == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }
#endif

  // Initialize verification result to false by default.
  *verification_result = kHardenedBoolFalse;

  // Call the unified `finalize` operation, which will determine the RSA size
  // based on the mode stored in OTBN.
  HARDENED_TRY_WIPE_DMEM(rsa_signature_verify_finalize(
      message_digest, (rsa_signature_padding_t)padding_mode,
      verification_result));
  return otcrypto_eval_exit(OTCRYPTO_OK);
}

static otcrypto_status_t rsa_encrypt_exp_async_start(
    const otcrypto_unblinded_key_t *public_key, uint32_t exponent,
    const otcrypto_hash_mode_t hash_mode,
    const otcrypto_const_byte_buf_t *message,
    const otcrypto_const_byte_buf_t *label) {
  OTCRYPTO_SET_CMVP_INDICATOR(OTCRYPTO_FUNCTION_RSA_ENCRYPT_ASYNC_START);
  OTCRYPTO_LOCKED_STATE_CHECK();
#ifndef OTCRYPTO_DISABLE_NULL_CHECKS
  // Check for NULL pointers.
  if (public_key == NULL || public_key->key == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  if (message == NULL || ((message->data == NULL) && (message->len != 0))) {
    return OTCRYPTO_BAD_ARGS;
  }

  if (label == NULL || ((label->data == NULL) && (label->len != 0))) {
    return OTCRYPTO_BAD_ARGS;
  }
#endif

  // Check the caller-provided public key buffer.
  HARDENED_TRY(public_key_structural_check(public_key));

  // Verify the checksum.
  if (otcrypto_integrity_unblinded_key_check(public_key) != kHardenedBoolTrue) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Ensure the key is intended for encryption.
  if (launder32(public_key->key_mode) != kOtcryptoKeyModeRsaEncryptOaep) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(public_key->key_mode, kOtcryptoKeyModeRsaEncryptOaep);

  // Infer the RSA size from the public key.
  otcrypto_rsa_size_t size;
  HARDENED_TRY(rsa_size_from_public_key(public_key, &size));
  OTCRYPTO_HEALTH_CHECK(size == kOtcryptoRsaSize2048 ? kTestRsa2048VerifyBit
                                                     : kTestRsa4096VerifyBit);

  rsa_size_t rsa_size = (rsa_size_t)0;
  size_t num_words = 0;
  HARDENED_TRY(rsa_size_to_params(size, &rsa_size, &num_words));
  HARDENED_CHECK_EQ(public_key->key_length, num_words * sizeof(uint32_t));
  HARDENED_TRY_WIPE_DMEM(
      rsa_encrypt_start(rsa_size, exponent, public_key->key, hash_mode,
                        message->data, message->len, label->data, label->len));
  return otcrypto_eval_exit(OTCRYPTO_OK);
}

otcrypto_status_t otcrypto_rsa_encrypt_async_start(
    const otcrypto_unblinded_key_t *public_key,
    const otcrypto_hash_mode_t hash_mode,
    const otcrypto_const_byte_buf_t *message,
    const otcrypto_const_byte_buf_t *label) {
  return rsa_encrypt_exp_async_start(public_key, /*exponent=*/0, hash_mode,
                                     message, label);
}

otcrypto_status_t otcrypto_rsa_encrypt_async_finalize(
    otcrypto_word32_buf_t *ciphertext) {
  OTCRYPTO_SET_CMVP_INDICATOR(OTCRYPTO_FUNCTION_RSA_ENCRYPT_ASYNC_FINALIZE);
  OTCRYPTO_LOCKED_STATE_CHECK();
#ifndef OTCRYPTO_DISABLE_NULL_CHECKS
  // Check for NULL pointers.
  if (ciphertext == NULL || ciphertext->data == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }
#endif

  rsa_size_t rsa_size = (rsa_size_t)0;
  HARDENED_TRY(rsa_size_from_num_words(ciphertext->len, &rsa_size));
  HARDENED_TRY_WIPE_DMEM(rsa_encrypt_finalize(rsa_size, ciphertext->data));
  return otcrypto_eval_exit(OTCRYPTO_OK);
}

static otcrypto_status_t rsa_decrypt_exp_async_start(
    const otcrypto_blinded_key_t *private_key, uint32_t exponent,
    const otcrypto_const_word32_buf_t *ciphertext) {
  OTCRYPTO_SET_CMVP_INDICATOR(OTCRYPTO_FUNCTION_RSA_DECRYPT_ASYNC_START);
  OTCRYPTO_HEALTH_CHECK(kTestRsa4096SignBit);
#ifndef OTCRYPTO_DISABLE_NULL_CHECKS
  // Check for NULL pointers.
  if (private_key == NULL || private_key->keyblob == NULL ||
      ciphertext == NULL || ciphertext->data == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }
#endif

  // Infer the RSA size from the private key.
  otcrypto_rsa_size_t size;
  HARDENED_TRY(rsa_size_from_private_key(private_key, &size));

  // Check the caller-provided private key buffer.
  HARDENED_TRY(private_key_structural_check(size, private_key));

  // Verify the checksum.
  if (otcrypto_integrity_blinded_key_check(private_key) != kHardenedBoolTrue) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Ensure that the key is intended for encryption.
  if (launder32(private_key->config.key_mode) !=
      kOtcryptoKeyModeRsaEncryptOaep) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(private_key->config.key_mode,
                    kOtcryptoKeyModeRsaEncryptOaep);

  // Start the decryption routine.
  rsa_size_t rsa_size = (rsa_size_t)0;
  size_t num_words = 0;
  HARDENED_TRY(rsa_size_to_params(size, &rsa_size, &num_words));
  HARDENED_CHECK_EQ(private_key->keyblob_length,
                    (3 * num_words + 1) * sizeof(uint32_t));
  if (ciphertext->len != num_words) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(ciphertext->len, num_words);
  const uint32_t *d0 = private_key->keyblob;
  const uint32_t *d1 = &private_key->keyblob[num_words];
  const uint32_t *n = &private_key->keyblob[2 * num_words];
  uint32_t checksum = private_key->keyblob[3 * num_words];

  // Check that ciphertext is < n.
  if (bignum_lt(ciphertext->data, n, num_words) == kHardenedBoolFalse) {
    return OTCRYPTO_BAD_ARGS;
  }

  HARDENED_TRY_WIPE_DMEM(rsa_decrypt_start(rsa_size, d0, d1, exponent, n,
                                           ciphertext->data, checksum));
  return otcrypto_eval_exit(OTCRYPTO_OK);
}

otcrypto_status_t otcrypto_rsa_decrypt_async_start(
    const otcrypto_blinded_key_t *private_key,
    const otcrypto_const_word32_buf_t *ciphertext) {
  return rsa_decrypt_exp_async_start(private_key, /*exponent=*/0, ciphertext);
}

otcrypto_status_t otcrypto_rsa_decrypt_async_finalize(
    const otcrypto_hash_mode_t hash_mode,
    const otcrypto_const_byte_buf_t *label, otcrypto_byte_buf_t *plaintext,
    size_t *plaintext_bytelen) {
  OTCRYPTO_SET_CMVP_INDICATOR(OTCRYPTO_FUNCTION_RSA_DECRYPT_ASYNC_FINALIZE);
  OTCRYPTO_LOCKED_STATE_CHECK();
#ifndef OTCRYPTO_DISABLE_NULL_CHECKS
  if (plaintext == NULL || plaintext->data == NULL || label == NULL ||
      (label->data == NULL && label->len != 0) || plaintext_bytelen == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }
#endif

  // Call the unified `finalize()` operation, which will infer the RSA size
  // from OTBN.
  HARDENED_TRY_WIPE_DMEM(
      rsa_decrypt_finalize(hash_mode, label->data, label->len, plaintext->len,
                           plaintext->data, plaintext_bytelen));

  // Consistency check; this should never happen.
  if (launder32(*plaintext_bytelen) > plaintext->len) {
    HARDENED_TRAP();
    // COVERAGE (FI CM) Unreachable code, checked against fault injections.
    return OTCRYPTO_FATAL_ERR;
  }
  HARDENED_CHECK_LE(*plaintext_bytelen, plaintext->len);

  return otcrypto_eval_exit(OTCRYPTO_OK);
}

static status_t public_exponent_check(uint32_t exponent) {
  if (launder32(exponent) < 3 || is_even(launder32(exponent))) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_GE(exponent, 3);
  HARDENED_CHECK_EQ(exponent & 1, 1);
  return OTCRYPTO_OK;
}

otcrypto_status_t otcrypto_rsa_sign_exp(
    const otcrypto_blinded_key_t *private_key, uint32_t exponent,
    const otcrypto_hash_digest_t message_digest,
    otcrypto_rsa_padding_t padding_mode, otcrypto_word32_buf_t *signature) {
  OTCRYPTO_SET_CMVP_INDICATOR(OTCRYPTO_FUNCTION_RSA_SIGN_EXP);
  HARDENED_TRY(public_exponent_check(exponent));
  HARDENED_TRY(rsa_sign_exp_async_start(private_key, exponent, message_digest,
                                        padding_mode));
  return otcrypto_eval_exit(otcrypto_rsa_sign_async_finalize(signature));
}

otcrypto_status_t otcrypto_rsa_verify_exp(
    const otcrypto_unblinded_key_t *public_key, uint32_t exponent,
    const otcrypto_hash_digest_t message_digest,
    otcrypto_rsa_padding_t padding_mode,
    const otcrypto_const_word32_buf_t *signature,
    hardened_bool_t *verification_result) {
  OTCRYPTO_SET_CMVP_INDICATOR(OTCRYPTO_FUNCTION_RSA_VERIFY_EXP);
  HARDENED_TRY(public_exponent_check(exponent));
  HARDENED_TRY(rsa_verify_exp_async_start(public_key, exponent, signature));
  HARDENED_TRY(key_mode_padding_check(public_key->key_mode, padding_mode));
  return otcrypto_eval_exit(otcrypto_rsa_verify_async_finalize(
      message_digest, padding_mode, verification_result));
}

otcrypto_status_t otcrypto_rsa_encrypt_exp(
    const otcrypto_unblinded_key_t *public_key, uint32_t exponent,
    const otcrypto_hash_mode_t hash_mode,
    const otcrypto_const_byte_buf_t *message,
    const otcrypto_const_byte_buf_t *label, otcrypto_word32_buf_t *ciphertext) {
  OTCRYPTO_SET_CMVP_INDICATOR(OTCRYPTO_FUNCTION_RSA_ENCRYPT_EXP);
  HARDENED_TRY(public_exponent_check(exponent));
  HARDENED_TRY(rsa_encrypt_exp_async_start(public_key, exponent, hash_mode,
                                           message, label));
  return otcrypto_eval_exit(otcrypto_rsa_encrypt_async_finalize(ciphertext));
}

otcrypto_status_t otcrypto_rsa_decrypt_exp(
    const otcrypto_blinded_key_t *private_key, uint32_t exponent,
    const otcrypto_hash_mode_t hash_mode,
    const otcrypto_const_word32_buf_t *ciphertext,
    const otcrypto_const_byte_buf_t *label, otcrypto_byte_buf_t *plaintext,
    size_t *plaintext_bytelen) {
  OTCRYPTO_SET_CMVP_INDICATOR(OTCRYPTO_FUNCTION_RSA_DECRYPT_EXP);
  HARDENED_TRY(public_exponent_check(exponent));
  HARDENED_TRY(rsa_decrypt_exp_async_start(private_key, exponent, ciphertext));
  return otcrypto_eval_exit(otcrypto_rsa_decrypt_async_finalize(
      hash_mode, label, plaintext, plaintext_bytelen));
}
