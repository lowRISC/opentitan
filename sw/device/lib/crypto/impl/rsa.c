// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/include/rsa.h"

#include "sw/device/lib/base/hardened_memory.h"
#include "sw/device/lib/crypto/drivers/entropy.h"
#include "sw/device/lib/crypto/impl/integrity.h"
#include "sw/device/lib/crypto/impl/rsa/rsa_keygen.h"
#include "sw/device/lib/crypto/impl/rsa/rsa_signature.h"
#include "sw/device/lib/crypto/impl/status.h"
#include "sw/device/lib/crypto/include/datatypes.h"

// Module ID for status codes.
#define MODULE_ID MAKE_MODULE_ID('r', 's', 'a')

static_assert(kRsa2048PublicKeyBytes == sizeof(rsa_2048_public_key_t),
              "RSA-2048 public key size mismatch.");
static_assert(kRsa3072PublicKeyBytes == sizeof(rsa_3072_public_key_t),
              "RSA-3072 public key size mismatch.");
static_assert(kRsa4096PublicKeyBytes == sizeof(rsa_4096_public_key_t),
              "RSA-4096 public key size mismatch.");
static_assert(kRsa2048PrivateKeyBytes == sizeof(rsa_2048_int_t),
              "RSA-2048 private key size mismatch.");
static_assert(kRsa3072PrivateKeyBytes == sizeof(rsa_3072_int_t),
              "RSA-3072 private key size mismatch.");
static_assert(kRsa4096PrivateKeyBytes == sizeof(rsa_4096_int_t),
              "RSA-4096 private key size mismatch.");
static_assert(kRsa2048PrivateKeyblobBytes == sizeof(rsa_2048_private_key_t),
              "RSA-2048 keyblob size mismatch.");
static_assert(kRsa3072PrivateKeyblobBytes == sizeof(rsa_3072_private_key_t),
              "RSA-3072 keyblob size mismatch.");
static_assert(kRsa4096PrivateKeyblobBytes == sizeof(rsa_4096_private_key_t),
              "RSA-4096 keyblob size mismatch.");

crypto_status_t otcrypto_rsa_keygen(rsa_size_t size,
                                    crypto_unblinded_key_t *public_key,
                                    crypto_blinded_key_t *private_key) {
  HARDENED_TRY(otcrypto_rsa_keygen_async_start(size));
  return otcrypto_rsa_keygen_async_finalize(public_key, private_key);
}

/**
 * Check if a key mode is intended for RSA.
 *
 * @param mode Mode to check.
 * @return OK if the mode is for RSA, OTCRYPTO_BAD_ARGS otherwise.
 */
static status_t rsa_mode_check(const key_mode_t mode) {
  switch (mode) {
    case kKeyModeRsaSignPkcs:
      return OTCRYPTO_OK;
    case kKeyModeRsaSignPss:
      return OTCRYPTO_OK;
    default:
      return OTCRYPTO_BAD_ARGS;
  }

  // Should be unreachable.
  HARDENED_TRAP();
  return OTCRYPTO_FATAL_ERR;
}

crypto_status_t otcrypto_rsa_public_key_construct(
    rsa_size_t size, crypto_const_word32_buf_t modulus, uint32_t exponent,
    crypto_unblinded_key_t *public_key) {
  if (modulus.data == NULL || public_key == NULL || public_key->key == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_TRY(rsa_mode_check(public_key->key_mode));

  switch (size) {
    case kRsaSize2048: {
      if (public_key->key_length != sizeof(rsa_2048_public_key_t) ||
          modulus.len != kRsa2048NumWords) {
        return OTCRYPTO_BAD_ARGS;
      }
      rsa_2048_public_key_t *pk = (rsa_2048_public_key_t *)public_key->key;
      pk->e = exponent;
      hardened_memcpy(pk->n.data, modulus.data, modulus.len);
      break;
    }
    case kRsaSize3072: {
      if (public_key->key_length != sizeof(rsa_3072_public_key_t) ||
          modulus.len != kRsa3072NumWords) {
        return OTCRYPTO_BAD_ARGS;
      }
      rsa_3072_public_key_t *pk = (rsa_3072_public_key_t *)public_key->key;
      pk->e = exponent;
      hardened_memcpy(pk->n.data, modulus.data, modulus.len);
      break;
    }
    case kRsaSize4096: {
      if (public_key->key_length != sizeof(rsa_4096_public_key_t) ||
          modulus.len != kRsa4096NumWords) {
        return OTCRYPTO_BAD_ARGS;
      }
      rsa_4096_public_key_t *pk = (rsa_4096_public_key_t *)public_key->key;
      pk->e = exponent;
      hardened_memcpy(pk->n.data, modulus.data, modulus.len);
      break;
    }
    default:
      return OTCRYPTO_BAD_ARGS;
  }

  public_key->checksum = integrity_unblinded_checksum(public_key);
  return OTCRYPTO_OK;
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
    const rsa_size_t size, const crypto_blinded_key_t *private_key) {
  // Check that the key mode is a valid RSA mode.
  HARDENED_TRY(rsa_mode_check(private_key->config.key_mode));

  // Sideloaded keys are not supported for RSA.
  if (private_key->config.hw_backed != kHardenedBoolFalse) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Check the lengths against the RSA size.
  size_t key_length = 0;
  size_t keyblob_length = 0;
  switch (launder32(size)) {
    case kRsaSize2048:
      HARDENED_CHECK_EQ(size, kRsaSize2048);
      key_length = kRsa2048PrivateKeyBytes;
      keyblob_length = kRsa2048PrivateKeyblobBytes;
      break;
    case kRsaSize3072:
      HARDENED_CHECK_EQ(size, kRsaSize3072);
      key_length = kRsa3072PrivateKeyBytes;
      keyblob_length = kRsa3072PrivateKeyblobBytes;
      break;
    case kRsaSize4096:
      HARDENED_CHECK_EQ(size, kRsaSize4096);
      key_length = kRsa4096PrivateKeyBytes;
      keyblob_length = kRsa4096PrivateKeyblobBytes;
      break;
    default:
      return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_NE(key_length, 0);
  HARDENED_CHECK_NE(keyblob_length, 0);

  if (private_key->config.key_length != key_length ||
      private_key->keyblob_length != keyblob_length) {
    return OTCRYPTO_BAD_ARGS;
  }

  return OTCRYPTO_OK;
}

crypto_status_t otcrypto_rsa_private_key_from_exponents(
    rsa_size_t size, crypto_const_word32_buf_t modulus, uint32_t e,
    crypto_const_word32_buf_t d_share0, crypto_const_word32_buf_t d_share1,
    crypto_blinded_key_t *private_key) {
  if (modulus.data == NULL || d_share0.data == NULL || d_share1.data == NULL ||
      private_key == NULL || private_key->keyblob == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_TRY(rsa_mode_check(private_key->config.key_mode));

  // Ensure that the length of the private exponent shares matches the length
  // of the modulus.
  if (d_share0.len != modulus.len || d_share1.len != modulus.len) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Check the public exponent is odd and greater than 2^16 (see FIPS 186-5,
  // section A.1.1).
  if ((e & 1) != 1 || e >> 16 == 0) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Check the mode and lengths for the private key.
  HARDENED_TRY(private_key_structural_check(size, private_key));

  switch (size) {
    case kRsaSize2048: {
      if (private_key->keyblob_length != sizeof(rsa_2048_private_key_t) ||
          modulus.len != kRsa2048NumWords) {
        return OTCRYPTO_BAD_ARGS;
      }
      rsa_2048_private_key_t *sk =
          (rsa_2048_private_key_t *)private_key->keyblob;
      hardened_memcpy(sk->n.data, modulus.data, modulus.len);
      hardened_memcpy(sk->d.data, d_share0.data, d_share0.len);
      // TODO: RSA keys are currently unblinded, so combine the shares.
      for (size_t i = 0; i < d_share1.len; i++) {
        sk->d.data[i] ^= d_share1.data[i];
      }
      break;
    }
    case kRsaSize3072: {
      if (private_key->keyblob_length != sizeof(rsa_3072_private_key_t) ||
          modulus.len != kRsa3072NumWords) {
        return OTCRYPTO_BAD_ARGS;
      }
      rsa_3072_private_key_t *sk =
          (rsa_3072_private_key_t *)private_key->keyblob;
      hardened_memcpy(sk->n.data, modulus.data, modulus.len);
      hardened_memcpy(sk->d.data, d_share0.data, d_share0.len);
      // TODO: RSA keys are currently unblinded, so combine the shares.
      for (size_t i = 0; i < d_share1.len; i++) {
        sk->d.data[i] ^= d_share1.data[i];
      }
      break;
    }
    case kRsaSize4096: {
      if (private_key->keyblob_length != sizeof(rsa_4096_private_key_t) ||
          modulus.len != kRsa4096NumWords) {
        return OTCRYPTO_BAD_ARGS;
      }
      rsa_4096_private_key_t *sk =
          (rsa_4096_private_key_t *)private_key->keyblob;
      hardened_memcpy(sk->n.data, modulus.data, modulus.len);
      hardened_memcpy(sk->d.data, d_share0.data, d_share0.len);
      // TODO: RSA keys are currently unblinded, so combine the shares.
      for (size_t i = 0; i < d_share1.len; i++) {
        sk->d.data[i] ^= d_share1.data[i];
      }
      break;
    }
    default:
      return OTCRYPTO_BAD_ARGS;
  }

  private_key->checksum = integrity_blinded_checksum(private_key);
  return OTCRYPTO_OK;
}

crypto_status_t otcrypto_rsa_sign(const crypto_blinded_key_t *private_key,
                                  const hash_digest_t *message_digest,
                                  rsa_padding_t padding_mode,
                                  crypto_word32_buf_t *signature) {
  HARDENED_TRY(
      otcrypto_rsa_sign_async_start(private_key, message_digest, padding_mode));
  return otcrypto_rsa_sign_async_finalize(signature);
}

crypto_status_t otcrypto_rsa_verify(const crypto_unblinded_key_t *public_key,
                                    const hash_digest_t *message_digest,
                                    rsa_padding_t padding_mode,
                                    crypto_const_word32_buf_t signature,
                                    hardened_bool_t *verification_result) {
  HARDENED_TRY(otcrypto_rsa_verify_async_start(public_key, signature));
  return otcrypto_rsa_verify_async_finalize(message_digest, padding_mode,
                                            verification_result);
}

/**
 * Infer the RSA key size from the length of the public key.
 *
 * @param public_key Public key.
 * @param[out] key_size RSA key size.
 * @return OK if the key is valid, OTCRYPTO_BAD_ARGS otherwise.
 */
static status_t rsa_size_from_public_key(
    const crypto_unblinded_key_t *public_key, rsa_size_t *key_size) {
  switch (launder32(public_key->key_length)) {
    case kRsa2048PublicKeyBytes:
      HARDENED_CHECK_EQ(public_key->key_length, kRsa2048PublicKeyBytes);
      *key_size = kRsaSize2048;
      return OTCRYPTO_OK;
    case kRsa3072PublicKeyBytes:
      HARDENED_CHECK_EQ(public_key->key_length, kRsa3072PublicKeyBytes);
      *key_size = kRsaSize3072;
      return OTCRYPTO_OK;
    case kRsa4096PublicKeyBytes:
      HARDENED_CHECK_EQ(public_key->key_length, kRsa4096PublicKeyBytes);
      *key_size = kRsaSize4096;
      return OTCRYPTO_OK;
    default:
      // No matches.
      return OTCRYPTO_BAD_ARGS;
  }

  // Should be unreachable.
  HARDENED_TRAP();
  return OTCRYPTO_FATAL_ERR;
}

/**
 * Infer the RSA key size from the length of the private key.
 *
 * @param private_key Private key.
 * @param[out] key_size RSA key size.
 * @return OK if the key is valid, OTCRYPTO_BAD_ARGS otherwise.
 */
static status_t rsa_size_from_private_key(
    const crypto_blinded_key_t *private_key, rsa_size_t *key_size) {
  switch (launder32(private_key->config.key_length)) {
    case kRsa2048PrivateKeyBytes:
      HARDENED_CHECK_EQ(private_key->config.key_length,
                        kRsa2048PrivateKeyBytes);
      *key_size = kRsaSize2048;
      return OTCRYPTO_OK;
    case kRsa3072PrivateKeyBytes:
      HARDENED_CHECK_EQ(private_key->config.key_length,
                        kRsa3072PrivateKeyBytes);
      *key_size = kRsaSize3072;
      return OTCRYPTO_OK;
    case kRsa4096PrivateKeyBytes:
      HARDENED_CHECK_EQ(private_key->config.key_length,
                        kRsa4096PrivateKeyBytes);
      *key_size = kRsaSize4096;
      return OTCRYPTO_OK;
    default:
      // No matches.
      return OTCRYPTO_BAD_ARGS;
  }

  // Should be unreachable.
  HARDENED_TRAP();
  return OTCRYPTO_FATAL_ERR;
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
    const crypto_unblinded_key_t *public_key) {
  // Check that the key mode is a valid RSA mode.
  return rsa_mode_check(public_key->key_mode);
}

crypto_status_t otcrypto_rsa_keygen_async_start(rsa_size_t size) {
  // Check that the entropy complex is initialized.
  HARDENED_TRY(entropy_complex_check());

  switch (size) {
    case kRsaSize2048:
      return rsa_keygen_2048_start();
    case kRsaSize3072:
      return rsa_keygen_3072_start();
    case kRsaSize4096:
      return rsa_keygen_4096_start();
    default:
      return OTCRYPTO_BAD_ARGS;
  }

  // Should be unreachable.
  HARDENED_TRAP();
  return OTCRYPTO_FATAL_ERR;
}

crypto_status_t otcrypto_rsa_keygen_async_finalize(
    crypto_unblinded_key_t *public_key, crypto_blinded_key_t *private_key) {
  // Check for NULL pointers.
  if (public_key == NULL || public_key->key == NULL || private_key == NULL ||
      private_key->keyblob == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }
  // Infer the RSA size from the public key modulus.
  rsa_size_t size;
  HARDENED_TRY(rsa_size_from_public_key(public_key, &size));

  // Check the caller-provided public key buffer.
  HARDENED_TRY(public_key_structural_check(public_key));

  // Check the caller-provided private key buffer.
  HARDENED_TRY(private_key_structural_check(size, private_key));

  // Call the required finalize() operation.
  switch (size) {
    case kRsaSize2048: {
      // Finalize the keygen operation and retrieve the keys.
      rsa_2048_public_key_t *pk = (rsa_2048_public_key_t *)public_key->key;
      rsa_2048_private_key_t *sk =
          (rsa_2048_private_key_t *)private_key->keyblob;
      HARDENED_TRY(rsa_keygen_2048_finalize(pk, sk));
      break;
    }
    case kRsaSize3072: {
      // Finalize the keygen operation and retrieve the keys.
      rsa_3072_public_key_t *pk = (rsa_3072_public_key_t *)public_key->key;
      rsa_3072_private_key_t *sk =
          (rsa_3072_private_key_t *)private_key->keyblob;
      HARDENED_TRY(rsa_keygen_3072_finalize(pk, sk));
      break;
    }
    case kRsaSize4096: {
      // Finalize the keygen operation and retrieve the keys.
      rsa_4096_public_key_t *pk = (rsa_4096_public_key_t *)public_key->key;
      rsa_4096_private_key_t *sk =
          (rsa_4096_private_key_t *)private_key->keyblob;
      HARDENED_TRY(rsa_keygen_4096_finalize(pk, sk));
      break;
    }
    default:
      // Invalid key size.
      return OTCRYPTO_BAD_ARGS;
  }

  // Construct checksums for the new keys.
  public_key->checksum = integrity_unblinded_checksum(public_key);
  private_key->checksum = integrity_blinded_checksum(private_key);

  return OTCRYPTO_OK;
}

crypto_status_t otcrypto_rsa_sign_async_start(
    const crypto_blinded_key_t *private_key,
    const hash_digest_t *message_digest, rsa_padding_t padding_mode) {
  // Check for NULL pointers.
  if (message_digest == NULL || message_digest->data == NULL ||
      private_key == NULL || private_key->keyblob == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Infer the RSA size from the private key.
  rsa_size_t size;
  HARDENED_TRY(rsa_size_from_private_key(private_key, &size));

  // Check the caller-provided private key buffer.
  HARDENED_TRY(private_key_structural_check(size, private_key));

  // Verify the checksum.
  if (integrity_blinded_key_check(private_key) != kHardenedBoolTrue) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Start the appropriate signature generation routine.
  switch (size) {
    case kRsaSize2048: {
      rsa_2048_private_key_t *sk =
          (rsa_2048_private_key_t *)private_key->keyblob;
      return rsa_signature_generate_2048_start(
          sk, message_digest, (rsa_signature_padding_t)padding_mode);
    }
    case kRsaSize3072: {
      rsa_3072_private_key_t *sk =
          (rsa_3072_private_key_t *)private_key->keyblob;
      return rsa_signature_generate_3072_start(
          sk, message_digest, (rsa_signature_padding_t)padding_mode);
    }
    case kRsaSize4096: {
      rsa_4096_private_key_t *sk =
          (rsa_4096_private_key_t *)private_key->keyblob;
      return rsa_signature_generate_4096_start(
          sk, message_digest, (rsa_signature_padding_t)padding_mode);
    }
    default:
      // Invalid key size. Since the size was inferred, should be unreachable.
      HARDENED_TRAP();
      return OTCRYPTO_FATAL_ERR;
  }

  // Should be unreachable.
  HARDENED_TRAP();
  return OTCRYPTO_FATAL_ERR;
}

crypto_status_t otcrypto_rsa_sign_async_finalize(
    crypto_word32_buf_t *signature) {
  // Check for NULL pointers.
  if (signature == NULL || signature->data == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Determine the size based on the signature buffer length.
  switch (signature->len) {
    case kRsa2048NumWords:
      return rsa_signature_generate_2048_finalize(
          (rsa_2048_int_t *)signature->data);
    case kRsa3072NumWords:
      return rsa_signature_generate_3072_finalize(
          (rsa_3072_int_t *)signature->data);
    case kRsa4096NumWords:
      return rsa_signature_generate_4096_finalize(
          (rsa_4096_int_t *)signature->data);
    default:
      return OTCRYPTO_BAD_ARGS;
  }

  // Should be unreachable.
  HARDENED_TRAP();
  return OTCRYPTO_FATAL_ERR;
}

crypto_status_t otcrypto_rsa_verify_async_start(
    const crypto_unblinded_key_t *public_key,
    crypto_const_word32_buf_t signature) {
  // Check for NULL pointers.
  if (public_key == NULL || public_key->key == NULL || signature.data == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Check the caller-provided public key buffer.
  HARDENED_TRY(public_key_structural_check(public_key));

  // Verify the checksum.
  if (integrity_unblinded_key_check(public_key) != kHardenedBoolTrue) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Infer the RSA size from the public key.
  rsa_size_t size;
  HARDENED_TRY(rsa_size_from_public_key(public_key, &size));

  switch (size) {
    case kRsaSize2048: {
      if (signature.len != kRsa2048NumWords) {
        return OTCRYPTO_BAD_ARGS;
      }
      rsa_2048_public_key_t *pk = (rsa_2048_public_key_t *)public_key->key;
      rsa_2048_int_t *sig = (rsa_2048_int_t *)signature.data;
      return rsa_signature_verify_2048_start(pk, sig);
    }
    case kRsaSize3072: {
      if (signature.len != kRsa3072NumWords) {
        return OTCRYPTO_BAD_ARGS;
      }
      rsa_3072_public_key_t *pk = (rsa_3072_public_key_t *)public_key->key;
      rsa_3072_int_t *sig = (rsa_3072_int_t *)signature.data;
      return rsa_signature_verify_3072_start(pk, sig);
    }
    case kRsaSize4096: {
      if (signature.len != kRsa4096NumWords) {
        return OTCRYPTO_BAD_ARGS;
      }
      rsa_4096_public_key_t *pk = (rsa_4096_public_key_t *)public_key->key;
      rsa_4096_int_t *sig = (rsa_4096_int_t *)signature.data;
      return rsa_signature_verify_4096_start(pk, sig);
    }
    default:
      // Invalid key size. Since the size was inferred, should be unreachable.
      HARDENED_TRAP();
      return OTCRYPTO_FATAL_ERR;
  }

  // Should be unreachable.
  HARDENED_TRAP();
  return OTCRYPTO_FATAL_ERR;
}

crypto_status_t otcrypto_rsa_verify_async_finalize(
    const hash_digest_t *message_digest, rsa_padding_t padding_mode,
    hardened_bool_t *verification_result) {
  // Check for NULL pointers.
  if (message_digest == NULL || message_digest->data == NULL ||
      verification_result == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Initialize verification result to false by default.
  *verification_result = kHardenedBoolFalse;

  // Call the unified `finalize` operation, which will determine the RSA size
  // based on the mode stored in OTBN.
  return rsa_signature_verify_finalize(message_digest,
                                       (rsa_signature_padding_t)padding_mode,
                                       verification_result);
}
