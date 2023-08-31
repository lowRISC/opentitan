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

crypto_status_t otcrypto_rsa_keygen(rsa_key_size_t required_key_len,
                                    rsa_public_key_t *rsa_public_key,
                                    rsa_private_key_t *rsa_private_key) {
  HARDENED_TRY(otcrypto_rsa_keygen_async_start(required_key_len));
  return otcrypto_rsa_keygen_async_finalize(rsa_public_key, rsa_private_key);
}

crypto_status_t otcrypto_rsa_sign(const rsa_private_key_t *rsa_private_key,
                                  crypto_const_byte_buf_t input_message,
                                  rsa_padding_t padding_mode,
                                  rsa_hash_t hash_mode,
                                  crypto_word_buf_t *signature) {
  HARDENED_TRY(otcrypto_rsa_sign_async_start(rsa_private_key, input_message,
                                             padding_mode, hash_mode));
  return otcrypto_rsa_sign_async_finalize(signature);
}

crypto_status_t otcrypto_rsa_verify(const rsa_public_key_t *rsa_public_key,
                                    crypto_const_byte_buf_t input_message,
                                    rsa_padding_t padding_mode,
                                    rsa_hash_t hash_mode,
                                    crypto_const_word_buf_t signature,
                                    hardened_bool_t *verification_result) {
  HARDENED_TRY(otcrypto_rsa_verify_async_start(rsa_public_key, signature));
  return otcrypto_rsa_verify_async_finalize(input_message, padding_mode,
                                            hash_mode, verification_result);
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
      // TODO: PSS padding mode is not yet implemented.
      return OTCRYPTO_NOT_IMPLEMENTED;
    default:
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
    const rsa_public_key_t *public_key) {
  // Check for NULL pointers.
  if (public_key == NULL || public_key->n.key == NULL ||
      public_key->e.key == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Check that the modulus key mode is a valid RSA mode.
  HARDENED_TRY(rsa_mode_check(public_key->n.key_mode));

  // Check that the key modes match each other.
  if (public_key->n.key_mode != public_key->e.key_mode) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Check the size of the public exponent (should always be one 32b integer).
  if (public_key->e.key_length != sizeof(uint32_t)) {
    return OTCRYPTO_BAD_ARGS;
  }

  return OTCRYPTO_OK;
}

/**
 * Basic structural validity checks for RSA private key buffers.
 *
 * Checks for NULL pointers or invalid key modes. Does not verify checksums
 * or actual key data requirements because this routine is used for keygen as
 * well as other operations, when the key data is not yet populated.
 *
 * @param private_key Key to check.
 * @return OK if the key is valid, OTCRYPTO_BAD_ARGS otherwise.
 */
static status_t private_key_structural_check(
    const rsa_private_key_t *private_key) {
  // Check for NULL pointers.
  if (private_key == NULL || private_key->n.key == NULL ||
      private_key->d.keyblob == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Check that the modulus key mode is a valid RSA mode.
  HARDENED_TRY(rsa_mode_check(private_key->n.key_mode));

  // Check that the key modes match each other.
  if (private_key->n.key_mode != private_key->d.config.key_mode) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Sideloaded keys are not supported for RSA.
  if (private_key->d.config.hw_backed != kHardenedBoolFalse) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Check that the unblinded size for the private exponent matches the length
  // of the modulus.
  if (private_key->d.config.key_length != private_key->n.key_length) {
    return OTCRYPTO_BAD_ARGS;
  }

  return OTCRYPTO_OK;
}

/**
 * Infer the RSA key size from the length of the modulus buffer.
 *
 * @param modulus Modulus buffer.
 * @param[out] key_size RSA key size.
 * @return OK if the key is valid, OTCRYPTO_BAD_ARGS otherwise.
 */
static status_t key_length_from_modulus(const crypto_unblinded_key_t *modulus,
                                        rsa_key_size_t *key_size) {
  switch (modulus->key_length) {
    case kRsa2048NumBytes:
      *key_size = kRsaKeySize2048;
      break;
    case kRsa3072NumBytes:
      *key_size = kRsaKeySize3072;
      break;
    case kRsa4096NumBytes:
      *key_size = kRsaKeySize4096;
      break;
    default:
      return OTCRYPTO_BAD_ARGS;
  }
  return OTCRYPTO_OK;
}

crypto_status_t otcrypto_rsa_keygen_async_start(
    rsa_key_size_t required_key_len) {
  // Check that the entropy complex is initialized.
  HARDENED_TRY(entropy_complex_check());

  switch (required_key_len) {
    case kRsaKeySize2048:
      return rsa_keygen_2048_start();
    case kRsaKeySize3072:
      // TODO: connect RSA-3K to API.
      return OTCRYPTO_NOT_IMPLEMENTED;
    case kRsaKeySize4096:
      // TODO: connect RSA-4K to API.
      return OTCRYPTO_NOT_IMPLEMENTED;
    default:
      return OTCRYPTO_BAD_ARGS;
  }

  // Should be unreachable.
  HARDENED_TRAP();
  return OTCRYPTO_FATAL_ERR;
}

crypto_status_t otcrypto_rsa_keygen_async_finalize(
    rsa_public_key_t *rsa_public_key, rsa_private_key_t *rsa_private_key) {
  // Check the caller-provided public key buffer.
  HARDENED_TRY(public_key_structural_check(rsa_public_key));

  // Check the caller-provided private key buffer.
  HARDENED_TRY(private_key_structural_check(rsa_private_key));

  // Infer the key length from the public key modulus.
  rsa_key_size_t key_len;
  HARDENED_TRY(key_length_from_modulus(&rsa_public_key->n, &key_len));

  // Infer the key length from the private key modulus and ensure it matches.
  rsa_key_size_t key_len_private;
  HARDENED_TRY(key_length_from_modulus(&rsa_private_key->n, &key_len_private));
  if (key_len != key_len_private) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Call the required finalize() operation.
  // TODO: the private exponent is not currently blinded; data is copied to the
  // keyblob directly.
  switch (key_len) {
    case kRsaKeySize2048: {
      // Finalize the keygen operation and retrieve the keys.
      rsa_2048_public_key_t public_key2k;
      rsa_2048_private_key_t private_key2k;
      HARDENED_TRY(rsa_keygen_2048_finalize(&public_key2k, &private_key2k));

      // Copy the keys into the caller-allocated structs.
      hardened_memcpy(rsa_public_key->n.key, public_key2k.n.data,
                      kRsa2048NumWords);
      rsa_public_key->e.key[0] = public_key2k.e;
      hardened_memcpy(rsa_private_key->n.key, private_key2k.n.data,
                      kRsa2048NumWords);
      hardened_memcpy(rsa_private_key->d.keyblob, private_key2k.d.data,
                      kRsa2048NumWords);
      break;
    }
    case kRsaKeySize3072:
      // TODO: connect RSA-3K to API.
      return OTCRYPTO_NOT_IMPLEMENTED;
    case kRsaKeySize4096:
      // TODO: connect RSA-4K to API.
      return OTCRYPTO_NOT_IMPLEMENTED;
    default:
      // Invalid key size.
      return OTCRYPTO_BAD_ARGS;
  }

  // Construct checksums for all the new keys.
  rsa_public_key->n.checksum = integrity_unblinded_checksum(&rsa_public_key->n);
  rsa_public_key->e.checksum = integrity_unblinded_checksum(&rsa_public_key->e);
  rsa_private_key->n.checksum =
      integrity_unblinded_checksum(&rsa_private_key->n);
  rsa_private_key->d.checksum = integrity_blinded_checksum(&rsa_private_key->d);

  // Extra sanity check that the public modulus is equal for the public/private
  // key; the checksums should be exactly the same.
  if (rsa_private_key->n.checksum != rsa_public_key->n.checksum) {
    return OTCRYPTO_FATAL_ERR;
  }

  return OTCRYPTO_OK;
}

crypto_status_t otcrypto_rsa_sign_async_start(
    const rsa_private_key_t *rsa_private_key,
    crypto_const_byte_buf_t input_message, rsa_padding_t padding_mode,
    rsa_hash_t hash_mode) {
  // Check the caller-provided private key buffer.
  HARDENED_TRY(private_key_structural_check(rsa_private_key));

  // Check for NULL input buffer.
  if (input_message.len != 0 && input_message.data == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Verify the checksum for the modulus.
  if (integrity_unblinded_key_check(&rsa_private_key->n) != kHardenedBoolTrue) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Verify the checksum for the exponent.
  if (integrity_blinded_key_check(&rsa_private_key->d) != kHardenedBoolTrue) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Infer the key length from the private key modulus.
  rsa_key_size_t key_len;
  HARDENED_TRY(key_length_from_modulus(&rsa_private_key->n, &key_len));

  switch (key_len) {
    case kRsaKeySize2048: {
      // Construct the private key.
      rsa_2048_private_key_t private_key2k;
      hardened_memcpy(private_key2k.n.data, rsa_private_key->n.key,
                      kRsa2048NumWords);
      hardened_memcpy(private_key2k.d.data, rsa_private_key->d.keyblob,
                      kRsa2048NumWords);

      // Start signature generation.
      return rsa_signature_generate_2048_start(
          &private_key2k, input_message.data, input_message.len,
          (rsa_signature_padding_t)padding_mode,
          (rsa_signature_hash_t)hash_mode);
    }
    case kRsaKeySize3072:
      // TODO: connect RSA-3K to API.
      return OTCRYPTO_NOT_IMPLEMENTED;
    case kRsaKeySize4096:
      // TODO: connect RSA-4K to API.
      return OTCRYPTO_NOT_IMPLEMENTED;
    default:
      // Invalid key size.
      return OTCRYPTO_BAD_ARGS;
  }

  // Should be unreachable.
  HARDENED_TRAP();
  return OTCRYPTO_FATAL_ERR;
}

crypto_status_t otcrypto_rsa_sign_async_finalize(crypto_word_buf_t *signature) {
  // Check for NULL pointers.
  if (signature == NULL || signature->data == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Determine the size based on the signature buffer length.
  switch (signature->len) {
    case kRsa2048NumWords: {
      rsa_2048_int_t sig;
      HARDENED_TRY(rsa_signature_generate_2048_finalize(&sig));
      hardened_memcpy(signature->data, sig.data, kRsa2048NumWords);
      break;
    }
    case kRsa3072NumBytes:
      // TODO: connect RSA-3K to API.
      return OTCRYPTO_NOT_IMPLEMENTED;
    case kRsa4096NumBytes:
      // TODO: connect RSA-4K to API.
      return OTCRYPTO_NOT_IMPLEMENTED;
    default:
      return OTCRYPTO_BAD_ARGS;
  }
  return OTCRYPTO_OK;
}

crypto_status_t otcrypto_rsa_verify_async_start(
    const rsa_public_key_t *rsa_public_key, crypto_const_word_buf_t signature) {
  // Check the caller-provided public key buffer.
  HARDENED_TRY(public_key_structural_check(rsa_public_key));

  // Check for NULL pointers.
  if (signature.data == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Verify the checksum for the modulus.
  if (integrity_unblinded_key_check(&rsa_public_key->n) != kHardenedBoolTrue) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Verify the checksum for the exponent.
  if (integrity_unblinded_key_check(&rsa_public_key->e) != kHardenedBoolTrue) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Infer the key length from the public key modulus.
  rsa_key_size_t key_len;
  HARDENED_TRY(key_length_from_modulus(&rsa_public_key->n, &key_len));

  switch (key_len) {
    case kRsaKeySize2048: {
      // Construct the public key.
      rsa_2048_public_key_t public_key2k;
      hardened_memcpy(public_key2k.n.data, rsa_public_key->n.key,
                      kRsa2048NumWords);
      public_key2k.e = rsa_public_key->e.key[0];

      // Construct the signature buffer.
      if (signature.len != kRsa2048NumWords) {
        return OTCRYPTO_BAD_ARGS;
      }
      rsa_2048_int_t sig2k;
      hardened_memcpy(sig2k.data, signature.data, kRsa2048NumWords);

      // Start signature verification.
      return rsa_signature_verify_2048_start(&public_key2k, &sig2k);
    }
    case kRsaKeySize3072:
      // TODO: connect RSA-3K to API.
      return OTCRYPTO_NOT_IMPLEMENTED;
    case kRsaKeySize4096:
      // TODO: connect RSA-4K to API.
      return OTCRYPTO_NOT_IMPLEMENTED;
    default:
      // Invalid key size.
      return OTCRYPTO_BAD_ARGS;
  }

  // Should be unreachable.
  HARDENED_TRAP();
  return OTCRYPTO_FATAL_ERR;
}

crypto_status_t otcrypto_rsa_verify_async_finalize(
    crypto_const_byte_buf_t input_message, rsa_padding_t padding_mode,
    rsa_hash_t hash_mode, hardened_bool_t *verification_result) {
  // Initialize verification result to false by default.
  *verification_result = kHardenedBoolFalse;

  // Check for NULL pointers.
  if (input_message.len != 0 && input_message.data == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }
  if (verification_result == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Call the unified `finalize` operation, which will determine the RSA size
  // based on the mode stored in OTBN.
  return rsa_signature_verify_finalize(input_message.data, input_message.len,
                                       (rsa_signature_padding_t)padding_mode,
                                       (rsa_signature_hash_t)hash_mode,
                                       verification_result);
}
