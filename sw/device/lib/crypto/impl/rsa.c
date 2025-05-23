// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/include/rsa.h"

#include "sw/device/lib/base/hardened_memory.h"
#include "sw/device/lib/base/math.h"
#include "sw/device/lib/crypto/drivers/entropy.h"
#include "sw/device/lib/crypto/impl/integrity.h"
#include "sw/device/lib/crypto/impl/rsa/rsa_encryption.h"
#include "sw/device/lib/crypto/impl/rsa/rsa_keygen.h"
#include "sw/device/lib/crypto/impl/rsa/rsa_signature.h"
#include "sw/device/lib/crypto/impl/status.h"
#include "sw/device/lib/crypto/include/datatypes.h"

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

otcrypto_status_t otcrypto_rsa_keygen(otcrypto_rsa_size_t size,
                                      otcrypto_unblinded_key_t *public_key,
                                      otcrypto_blinded_key_t *private_key) {
  HARDENED_TRY(otcrypto_rsa_keygen_async_start(size));
  return otcrypto_rsa_keygen_async_finalize(public_key, private_key);
}

/**
 * Check if a key mode is intended for RSA.
 *
 * @param mode Mode to check.
 * @return OK if the mode is for RSA, OTCRYPTO_BAD_ARGS otherwise.
 */
static status_t rsa_mode_check(const otcrypto_key_mode_t mode) {
  switch (mode) {
    case kOtcryptoKeyModeRsaSignPkcs:
      return OTCRYPTO_OK;
    case kOtcryptoKeyModeRsaSignPss:
      return OTCRYPTO_OK;
    case kOtcryptoKeyModeRsaEncryptOaep:
      return OTCRYPTO_OK;
    default:
      return OTCRYPTO_BAD_ARGS;
  }

  // Should be unreachable.
  HARDENED_TRAP();
  return OTCRYPTO_FATAL_ERR;
}

otcrypto_status_t otcrypto_rsa_public_key_construct(
    otcrypto_rsa_size_t size, otcrypto_const_word32_buf_t modulus,
    uint32_t exponent, otcrypto_unblinded_key_t *public_key) {
  if (modulus.data == NULL || public_key == NULL || public_key->key == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }
  // Entropy complex must be initialized for `hardened_memcpy`.
  HARDENED_TRY(entropy_complex_check());

  HARDENED_TRY(rsa_mode_check(public_key->key_mode));

  switch (size) {
    case kOtcryptoRsaSize2048: {
      if (public_key->key_length != sizeof(rsa_2048_public_key_t) ||
          modulus.len != kRsa2048NumWords) {
        return OTCRYPTO_BAD_ARGS;
      }
      rsa_2048_public_key_t *pk = (rsa_2048_public_key_t *)public_key->key;
      pk->e = exponent;
      hardened_memcpy(pk->n.data, modulus.data, modulus.len);
      break;
    }
    case kOtcryptoRsaSize3072: {
      if (public_key->key_length != sizeof(rsa_3072_public_key_t) ||
          modulus.len != kRsa3072NumWords) {
        return OTCRYPTO_BAD_ARGS;
      }
      rsa_3072_public_key_t *pk = (rsa_3072_public_key_t *)public_key->key;
      pk->e = exponent;
      hardened_memcpy(pk->n.data, modulus.data, modulus.len);
      break;
    }
    case kOtcryptoRsaSize4096: {
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
    const otcrypto_rsa_size_t size, const otcrypto_blinded_key_t *private_key) {
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
    case kOtcryptoRsaSize2048:
      HARDENED_CHECK_EQ(size, kOtcryptoRsaSize2048);
      key_length = kOtcryptoRsa2048PrivateKeyBytes;
      keyblob_length = kOtcryptoRsa2048PrivateKeyblobBytes;
      break;
    case kOtcryptoRsaSize3072:
      HARDENED_CHECK_EQ(size, kOtcryptoRsaSize3072);
      key_length = kOtcryptoRsa3072PrivateKeyBytes;
      keyblob_length = kOtcryptoRsa3072PrivateKeyblobBytes;
      break;
    case kOtcryptoRsaSize4096:
      HARDENED_CHECK_EQ(size, kOtcryptoRsaSize4096);
      key_length = kOtcryptoRsa4096PrivateKeyBytes;
      keyblob_length = kOtcryptoRsa4096PrivateKeyblobBytes;
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

otcrypto_status_t otcrypto_rsa_private_key_from_exponents(
    otcrypto_rsa_size_t size, otcrypto_const_word32_buf_t modulus, uint32_t e,
    otcrypto_const_word32_buf_t d_share0, otcrypto_const_word32_buf_t d_share1,
    otcrypto_blinded_key_t *private_key) {
  if (modulus.data == NULL || d_share0.data == NULL || d_share1.data == NULL ||
      private_key == NULL || private_key->keyblob == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }
  // Entropy complex must be initialized for `hardened_memcpy`.
  HARDENED_TRY(entropy_complex_check());

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

  // Randomize the keyblob.
  hardened_memshred(private_key->keyblob,
                    ceil_div(private_key->keyblob_length, sizeof(uint32_t)));

  switch (size) {
    case kOtcryptoRsaSize2048: {
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
    case kOtcryptoRsaSize3072: {
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
    case kOtcryptoRsaSize4096: {
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

otcrypto_status_t otcrypto_rsa_keypair_from_cofactor(
    otcrypto_rsa_size_t size, otcrypto_const_word32_buf_t modulus, uint32_t e,
    otcrypto_const_word32_buf_t cofactor_share0,
    otcrypto_const_word32_buf_t cofactor_share1,
    otcrypto_unblinded_key_t *public_key, otcrypto_blinded_key_t *private_key) {
  HARDENED_TRY(otcrypto_rsa_keypair_from_cofactor_async_start(
      size, modulus, e, cofactor_share0, cofactor_share1));
  HARDENED_TRY(otcrypto_rsa_keypair_from_cofactor_async_finalize(public_key,
                                                                 private_key));

  // Entropy complex must be initialized for `hardened_memcpy`.
  HARDENED_TRY(entropy_complex_check());

  // Interpret the recomputed public key. Double-check the lengths to be safe,
  // but they should have been checked above already.
  hardened_bool_t modulus_eq = kHardenedBoolFalse;
  switch (size) {
    case kOtcryptoRsaSize2048: {
      if (public_key->key_length != sizeof(rsa_2048_public_key_t) ||
          modulus.len != kRsa2048NumWords) {
        return OTCRYPTO_RECOV_ERR;
      }
      rsa_2048_public_key_t *pk = (rsa_2048_public_key_t *)public_key->key;
      modulus_eq = hardened_memeq(modulus.data, pk->n.data, modulus.len);
      return OTCRYPTO_OK;
    }
    case kOtcryptoRsaSize3072:
      return OTCRYPTO_NOT_IMPLEMENTED;
    case kOtcryptoRsaSize4096:
      return OTCRYPTO_NOT_IMPLEMENTED;
    default:
      return OTCRYPTO_BAD_ARGS;
  }

  if (modulus_eq != kHardenedBoolTrue) {
    // This likely means that the cofactor/modulus combination was invalid,
    // for example the modulus was not divisible by the cofactor, or the
    // cofactor was too small.
    return OTCRYPTO_BAD_ARGS;
  }
  return OTCRYPTO_OK;
}

otcrypto_status_t otcrypto_rsa_sign(const otcrypto_blinded_key_t *private_key,
                                    const otcrypto_hash_digest_t message_digest,
                                    otcrypto_rsa_padding_t padding_mode,
                                    otcrypto_word32_buf_t signature) {
  HARDENED_TRY(
      otcrypto_rsa_sign_async_start(private_key, message_digest, padding_mode));
  return otcrypto_rsa_sign_async_finalize(signature);
}

otcrypto_status_t otcrypto_rsa_verify(
    const otcrypto_unblinded_key_t *public_key,
    const otcrypto_hash_digest_t message_digest,
    otcrypto_rsa_padding_t padding_mode, otcrypto_const_word32_buf_t signature,
    hardened_bool_t *verification_result) {
  HARDENED_TRY(otcrypto_rsa_verify_async_start(public_key, signature));
  return otcrypto_rsa_verify_async_finalize(message_digest, padding_mode,
                                            verification_result);
}

otcrypto_status_t otcrypto_rsa_encrypt(
    const otcrypto_unblinded_key_t *public_key,
    const otcrypto_hash_mode_t hash_mode, otcrypto_const_byte_buf_t message,
    otcrypto_const_byte_buf_t label, otcrypto_word32_buf_t ciphertext) {
  HARDENED_TRY(
      otcrypto_rsa_encrypt_async_start(public_key, hash_mode, message, label));
  return otcrypto_rsa_encrypt_async_finalize(ciphertext);
}

otcrypto_status_t otcrypto_rsa_decrypt(
    const otcrypto_blinded_key_t *private_key,
    const otcrypto_hash_mode_t hash_mode,
    otcrypto_const_word32_buf_t ciphertext, otcrypto_const_byte_buf_t label,
    otcrypto_byte_buf_t plaintext, size_t *plaintext_bytelen) {
  HARDENED_TRY(otcrypto_rsa_decrypt_async_start(private_key, ciphertext));
  return otcrypto_rsa_decrypt_async_finalize(hash_mode, label, plaintext,
                                             plaintext_bytelen);
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
  switch (launder32(public_key->key_length)) {
    case kOtcryptoRsa2048PublicKeyBytes:
      HARDENED_CHECK_EQ(public_key->key_length, kOtcryptoRsa2048PublicKeyBytes);
      *key_size = kOtcryptoRsaSize2048;
      return OTCRYPTO_OK;
    case kOtcryptoRsa3072PublicKeyBytes:
      HARDENED_CHECK_EQ(public_key->key_length, kOtcryptoRsa3072PublicKeyBytes);
      *key_size = kOtcryptoRsaSize3072;
      return OTCRYPTO_OK;
    case kOtcryptoRsa4096PublicKeyBytes:
      HARDENED_CHECK_EQ(public_key->key_length, kOtcryptoRsa4096PublicKeyBytes);
      *key_size = kOtcryptoRsaSize4096;
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
    const otcrypto_blinded_key_t *private_key, otcrypto_rsa_size_t *key_size) {
  switch (launder32(private_key->config.key_length)) {
    case kOtcryptoRsa2048PrivateKeyBytes:
      HARDENED_CHECK_EQ(private_key->config.key_length,
                        kOtcryptoRsa2048PrivateKeyBytes);
      *key_size = kOtcryptoRsaSize2048;
      return OTCRYPTO_OK;
    case kOtcryptoRsa3072PrivateKeyBytes:
      HARDENED_CHECK_EQ(private_key->config.key_length,
                        kOtcryptoRsa3072PrivateKeyBytes);
      *key_size = kOtcryptoRsaSize3072;
      return OTCRYPTO_OK;
    case kOtcryptoRsa4096PrivateKeyBytes:
      HARDENED_CHECK_EQ(private_key->config.key_length,
                        kOtcryptoRsa4096PrivateKeyBytes);
      *key_size = kOtcryptoRsaSize4096;
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
    const otcrypto_unblinded_key_t *public_key) {
  // Check that the key mode is a valid RSA mode.
  return rsa_mode_check(public_key->key_mode);
}

otcrypto_status_t otcrypto_rsa_keygen_async_start(otcrypto_rsa_size_t size) {
  // Check that the entropy complex is initialized.
  HARDENED_TRY(entropy_complex_check());

  switch (size) {
    case kOtcryptoRsaSize2048:
      return rsa_keygen_2048_start();
    case kOtcryptoRsaSize3072:
      return rsa_keygen_3072_start();
    case kOtcryptoRsaSize4096:
      return rsa_keygen_4096_start();
    default:
      return OTCRYPTO_BAD_ARGS;
  }

  // Should be unreachable.
  HARDENED_TRAP();
  return OTCRYPTO_FATAL_ERR;
}

otcrypto_status_t otcrypto_rsa_keygen_async_finalize(
    otcrypto_unblinded_key_t *public_key, otcrypto_blinded_key_t *private_key) {
  // Check for NULL pointers.
  if (public_key == NULL || public_key->key == NULL || private_key == NULL ||
      private_key->keyblob == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Check that the entropy complex is initialized.
  HARDENED_TRY(entropy_complex_check());

  // Infer the RSA size from the public key modulus.
  otcrypto_rsa_size_t size;
  HARDENED_TRY(rsa_size_from_public_key(public_key, &size));

  // Check the caller-provided public key buffer.
  HARDENED_TRY(public_key_structural_check(public_key));

  // Check the caller-provided private key buffer.
  HARDENED_TRY(private_key_structural_check(size, private_key));

  // Randomize the keyblob memory.
  hardened_memshred(private_key->keyblob,
                    ceil_div(private_key->keyblob_length, sizeof(uint32_t)));

  // Call the required finalize() operation.
  switch (size) {
    case kOtcryptoRsaSize2048: {
      // Finalize the keygen operation and retrieve the keys.
      rsa_2048_public_key_t *pk = (rsa_2048_public_key_t *)public_key->key;
      rsa_2048_private_key_t *sk =
          (rsa_2048_private_key_t *)private_key->keyblob;
      HARDENED_TRY(rsa_keygen_2048_finalize(pk, sk));
      break;
    }
    case kOtcryptoRsaSize3072: {
      // Finalize the keygen operation and retrieve the keys.
      rsa_3072_public_key_t *pk = (rsa_3072_public_key_t *)public_key->key;
      rsa_3072_private_key_t *sk =
          (rsa_3072_private_key_t *)private_key->keyblob;
      HARDENED_TRY(rsa_keygen_3072_finalize(pk, sk));
      break;
    }
    case kOtcryptoRsaSize4096: {
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

otcrypto_status_t otcrypto_rsa_keypair_from_cofactor_async_start(
    otcrypto_rsa_size_t size, otcrypto_const_word32_buf_t modulus, uint32_t e,
    otcrypto_const_word32_buf_t cofactor_share0,
    otcrypto_const_word32_buf_t cofactor_share1) {
  if (modulus.data == NULL || cofactor_share0.data == NULL ||
      cofactor_share1.data == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Entropy complex must be initialized for `hardened_memcpy`.
  HARDENED_TRY(entropy_complex_check());

  // Ensure that the length of the cofactor shares is half the length
  // of the modulus.
  if (cofactor_share0.len != modulus.len / 2 ||
      cofactor_share1.len != modulus.len / 2) {
    return OTCRYPTO_BAD_ARGS;
  }

  switch (size) {
    case kOtcryptoRsaSize2048: {
      if (cofactor_share0.len !=
              sizeof(rsa_2048_cofactor_t) / sizeof(uint32_t) ||
          modulus.len != kRsa2048NumWords) {
        return OTCRYPTO_BAD_ARGS;
      }
      rsa_2048_cofactor_t *cf = (rsa_2048_cofactor_t *)cofactor_share0.data;
      // TODO: RSA keys are currently unblinded, so combine the shares.
      for (size_t i = 0; i < cofactor_share1.len; i++) {
        cf->data[i] ^= cofactor_share1.data[i];
      }
      rsa_2048_public_key_t pk;
      hardened_memcpy(pk.n.data, modulus.data, modulus.len);
      pk.e = e;
      return rsa_keygen_from_cofactor_2048_start(&pk, cf);
    }
    case kOtcryptoRsaSize3072: {
      return OTCRYPTO_NOT_IMPLEMENTED;
    }
    case kOtcryptoRsaSize4096: {
      return OTCRYPTO_NOT_IMPLEMENTED;
    }
    default:
      return OTCRYPTO_BAD_ARGS;
  }

  // Should be unreachable.
  HARDENED_TRAP();
  return OTCRYPTO_FATAL_ERR;
}

otcrypto_status_t otcrypto_rsa_keypair_from_cofactor_async_finalize(
    otcrypto_unblinded_key_t *public_key, otcrypto_blinded_key_t *private_key) {
  // Check for NULL pointers.
  if (public_key == NULL || public_key->key == NULL || private_key == NULL ||
      private_key->keyblob == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Check that the entropy complex is initialized.
  HARDENED_TRY(entropy_complex_check());

  // Infer the RSA size from the public key modulus.
  otcrypto_rsa_size_t size;
  HARDENED_TRY(rsa_size_from_public_key(public_key, &size));

  // Check the caller-provided public key buffer.
  HARDENED_TRY(public_key_structural_check(public_key));

  // Check the caller-provided private key buffer.
  HARDENED_TRY(private_key_structural_check(size, private_key));

  // Randomize the keyblob memory.
  hardened_memshred(private_key->keyblob,
                    ceil_div(private_key->keyblob_length, sizeof(uint32_t)));

  // Call the required finalize() operation.
  switch (size) {
    case kOtcryptoRsaSize2048: {
      rsa_2048_public_key_t *pk = (rsa_2048_public_key_t *)public_key->key;
      rsa_2048_private_key_t *sk =
          (rsa_2048_private_key_t *)private_key->keyblob;
      HARDENED_TRY(rsa_keygen_from_cofactor_2048_finalize(pk, sk));
      break;
    }
    case kOtcryptoRsaSize3072: {
      return OTCRYPTO_NOT_IMPLEMENTED;
    }
    case kOtcryptoRsaSize4096: {
      return OTCRYPTO_NOT_IMPLEMENTED;
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
  return OTCRYPTO_FATAL_ERR;
}

otcrypto_status_t otcrypto_rsa_sign_async_start(
    const otcrypto_blinded_key_t *private_key,
    const otcrypto_hash_digest_t message_digest,
    otcrypto_rsa_padding_t padding_mode) {
  // Check for NULL pointers.
  if (message_digest.data == NULL || private_key == NULL ||
      private_key->keyblob == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Check that the entropy complex is initialized.
  HARDENED_TRY(entropy_complex_check());

  // Infer the RSA size from the private key.
  otcrypto_rsa_size_t size;
  HARDENED_TRY(rsa_size_from_private_key(private_key, &size));

  // Check the caller-provided private key buffer.
  HARDENED_TRY(private_key_structural_check(size, private_key));

  // Ensure the key mode matches the padding mode.
  HARDENED_TRY(
      key_mode_padding_check(private_key->config.key_mode, padding_mode));

  // Verify the checksum.
  if (integrity_blinded_key_check(private_key) != kHardenedBoolTrue) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Start the appropriate signature generation routine.
  switch (size) {
    case kOtcryptoRsaSize2048: {
      rsa_2048_private_key_t *sk =
          (rsa_2048_private_key_t *)private_key->keyblob;
      return rsa_signature_generate_2048_start(
          sk, message_digest, (rsa_signature_padding_t)padding_mode);
    }
    case kOtcryptoRsaSize3072: {
      rsa_3072_private_key_t *sk =
          (rsa_3072_private_key_t *)private_key->keyblob;
      return rsa_signature_generate_3072_start(
          sk, message_digest, (rsa_signature_padding_t)padding_mode);
    }
    case kOtcryptoRsaSize4096: {
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

otcrypto_status_t otcrypto_rsa_sign_async_finalize(
    otcrypto_word32_buf_t signature) {
  // Check for NULL pointers.
  if (signature.data == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Check that the entropy complex is initialized.
  HARDENED_TRY(entropy_complex_check());

  // Determine the size based on the signature buffer length.
  switch (signature.len) {
    case kRsa2048NumWords:
      return rsa_signature_generate_2048_finalize(
          (rsa_2048_int_t *)signature.data);
    case kRsa3072NumWords:
      return rsa_signature_generate_3072_finalize(
          (rsa_3072_int_t *)signature.data);
    case kRsa4096NumWords:
      return rsa_signature_generate_4096_finalize(
          (rsa_4096_int_t *)signature.data);
    default:
      return OTCRYPTO_BAD_ARGS;
  }

  // Should be unreachable.
  HARDENED_TRAP();
  return OTCRYPTO_FATAL_ERR;
}

otcrypto_status_t otcrypto_rsa_verify_async_start(
    const otcrypto_unblinded_key_t *public_key,
    otcrypto_const_word32_buf_t signature) {
  // Check for NULL pointers.
  if (public_key == NULL || public_key->key == NULL || signature.data == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Check that the entropy complex is initialized.
  HARDENED_TRY(entropy_complex_check());

  // Check the caller-provided public key buffer.
  HARDENED_TRY(public_key_structural_check(public_key));

  // Verify the checksum.
  if (integrity_unblinded_key_check(public_key) != kHardenedBoolTrue) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Infer the RSA size from the public key.
  otcrypto_rsa_size_t size;
  HARDENED_TRY(rsa_size_from_public_key(public_key, &size));

  switch (size) {
    case kOtcryptoRsaSize2048: {
      if (signature.len != kRsa2048NumWords) {
        return OTCRYPTO_BAD_ARGS;
      }
      rsa_2048_public_key_t *pk = (rsa_2048_public_key_t *)public_key->key;
      rsa_2048_int_t *sig = (rsa_2048_int_t *)signature.data;
      return rsa_signature_verify_2048_start(pk, sig);
    }
    case kOtcryptoRsaSize3072: {
      if (signature.len != kRsa3072NumWords) {
        return OTCRYPTO_BAD_ARGS;
      }
      rsa_3072_public_key_t *pk = (rsa_3072_public_key_t *)public_key->key;
      rsa_3072_int_t *sig = (rsa_3072_int_t *)signature.data;
      return rsa_signature_verify_3072_start(pk, sig);
    }
    case kOtcryptoRsaSize4096: {
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

otcrypto_status_t otcrypto_rsa_verify_async_finalize(
    const otcrypto_hash_digest_t message_digest,
    otcrypto_rsa_padding_t padding_mode, hardened_bool_t *verification_result) {
  // Check for NULL pointers.
  if (message_digest.data == NULL || verification_result == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Check that the entropy complex is initialized.
  HARDENED_TRY(entropy_complex_check());

  // Initialize verification result to false by default.
  *verification_result = kHardenedBoolFalse;

  // Call the unified `finalize` operation, which will determine the RSA size
  // based on the mode stored in OTBN.
  return rsa_signature_verify_finalize(message_digest,
                                       (rsa_signature_padding_t)padding_mode,
                                       verification_result);
}

otcrypto_status_t otcrypto_rsa_encrypt_async_start(
    const otcrypto_unblinded_key_t *public_key,
    const otcrypto_hash_mode_t hash_mode, otcrypto_const_byte_buf_t message,
    otcrypto_const_byte_buf_t label) {
  // Check for NULL pointers.
  if (public_key == NULL || public_key->key == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Check that the entropy complex is initialized.
  HARDENED_TRY(entropy_complex_check());

  if (message.data == NULL && (message.len != 0)) {
    return OTCRYPTO_BAD_ARGS;
  }

  if (label.data == NULL && (label.len != 0)) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Check the caller-provided public key buffer.
  HARDENED_TRY(public_key_structural_check(public_key));

  // Verify the checksum.
  if (integrity_unblinded_key_check(public_key) != kHardenedBoolTrue) {
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

  switch (launder32(size)) {
    case kOtcryptoRsaSize2048: {
      HARDENED_CHECK_EQ(size, kOtcryptoRsaSize2048);
      HARDENED_CHECK_EQ(public_key->key_length, sizeof(rsa_2048_public_key_t));
      rsa_2048_public_key_t *pk = (rsa_2048_public_key_t *)public_key->key;
      return rsa_encrypt_2048_start(pk, hash_mode, message.data, message.len,
                                    label.data, label.len);
    }
    case kOtcryptoRsaSize3072: {
      HARDENED_CHECK_EQ(size, kOtcryptoRsaSize3072);
      HARDENED_CHECK_EQ(public_key->key_length, sizeof(rsa_3072_public_key_t));
      rsa_3072_public_key_t *pk = (rsa_3072_public_key_t *)public_key->key;
      return rsa_encrypt_3072_start(pk, hash_mode, message.data, message.len,
                                    label.data, label.len);
    }
    case kOtcryptoRsaSize4096: {
      HARDENED_CHECK_EQ(size, kOtcryptoRsaSize4096);
      HARDENED_CHECK_EQ(public_key->key_length, sizeof(rsa_4096_public_key_t));
      rsa_4096_public_key_t *pk = (rsa_4096_public_key_t *)public_key->key;
      return rsa_encrypt_4096_start(pk, hash_mode, message.data, message.len,
                                    label.data, label.len);
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

otcrypto_status_t otcrypto_rsa_encrypt_async_finalize(
    otcrypto_word32_buf_t ciphertext) {
  // Check for NULL pointers.
  if (ciphertext.data == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Check that the entropy complex is initialized.
  HARDENED_TRY(entropy_complex_check());

  switch (launder32(ciphertext.len)) {
    case kRsa2048NumWords: {
      HARDENED_CHECK_EQ(ciphertext.len * sizeof(uint32_t),
                        sizeof(rsa_2048_int_t));
      rsa_2048_int_t *ctext = (rsa_2048_int_t *)ciphertext.data;
      return rsa_encrypt_2048_finalize(ctext);
    }
    case kRsa3072NumWords: {
      HARDENED_CHECK_EQ(ciphertext.len * sizeof(uint32_t),
                        sizeof(rsa_3072_int_t));
      rsa_3072_int_t *ctext = (rsa_3072_int_t *)ciphertext.data;
      return rsa_encrypt_3072_finalize(ctext);
    }
    case kRsa4096NumWords: {
      HARDENED_CHECK_EQ(ciphertext.len * sizeof(uint32_t),
                        sizeof(rsa_4096_int_t));
      rsa_4096_int_t *ctext = (rsa_4096_int_t *)ciphertext.data;
      return rsa_encrypt_4096_finalize(ctext);
    }
    default:
      return OTCRYPTO_BAD_ARGS;
  }

  // Should be unreachable.
  HARDENED_TRAP();
  return OTCRYPTO_FATAL_ERR;
}

otcrypto_status_t otcrypto_rsa_decrypt_async_start(
    const otcrypto_blinded_key_t *private_key,
    otcrypto_const_word32_buf_t ciphertext) {
  // Check for NULL pointers.
  if (private_key == NULL || private_key->keyblob == NULL ||
      ciphertext.data == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Check that the entropy complex is initialized.
  HARDENED_TRY(entropy_complex_check());

  // Infer the RSA size from the private key.
  otcrypto_rsa_size_t size;
  HARDENED_TRY(rsa_size_from_private_key(private_key, &size));

  // Check the caller-provided private key buffer.
  HARDENED_TRY(private_key_structural_check(size, private_key));

  // Verify the checksum.
  if (integrity_blinded_key_check(private_key) != kHardenedBoolTrue) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Ensure that the key is intended for encryption.
  if (launder32(private_key->config.key_mode) !=
      kOtcryptoKeyModeRsaEncryptOaep) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(private_key->config.key_mode,
                    kOtcryptoKeyModeRsaEncryptOaep);

  // Start the appropriate decryption routine.
  switch (launder32(size)) {
    case kOtcryptoRsaSize2048: {
      HARDENED_CHECK_EQ(size, kOtcryptoRsaSize2048);
      HARDENED_CHECK_EQ(private_key->keyblob_length,
                        sizeof(rsa_2048_private_key_t));
      if (ciphertext.len != kRsa2048NumWords) {
        return OTCRYPTO_BAD_ARGS;
      }
      rsa_2048_private_key_t *sk =
          (rsa_2048_private_key_t *)private_key->keyblob;
      rsa_2048_int_t *ctext = (rsa_2048_int_t *)ciphertext.data;
      return rsa_decrypt_2048_start(sk, ctext);
    }
    case kOtcryptoRsaSize3072: {
      HARDENED_CHECK_EQ(size, kOtcryptoRsaSize3072);
      HARDENED_CHECK_EQ(private_key->keyblob_length,
                        sizeof(rsa_3072_private_key_t));
      if (ciphertext.len != kRsa3072NumWords) {
        return OTCRYPTO_BAD_ARGS;
      }
      rsa_3072_private_key_t *sk =
          (rsa_3072_private_key_t *)private_key->keyblob;
      rsa_3072_int_t *ctext = (rsa_3072_int_t *)ciphertext.data;
      return rsa_decrypt_3072_start(sk, ctext);
    }
    case kOtcryptoRsaSize4096: {
      HARDENED_CHECK_EQ(size, kOtcryptoRsaSize4096);
      HARDENED_CHECK_EQ(private_key->keyblob_length,
                        sizeof(rsa_4096_private_key_t));
      if (ciphertext.len != kRsa4096NumWords) {
        return OTCRYPTO_BAD_ARGS;
      }
      rsa_4096_private_key_t *sk =
          (rsa_4096_private_key_t *)private_key->keyblob;
      rsa_4096_int_t *ctext = (rsa_4096_int_t *)ciphertext.data;
      return rsa_decrypt_4096_start(sk, ctext);
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

otcrypto_status_t otcrypto_rsa_decrypt_async_finalize(
    const otcrypto_hash_mode_t hash_mode, otcrypto_const_byte_buf_t label,
    otcrypto_byte_buf_t plaintext, size_t *plaintext_bytelen) {
  if (plaintext.data == NULL || label.data == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Check that the entropy complex is initialized.
  HARDENED_TRY(entropy_complex_check());

  // Call the unified `finalize()` operation, which will infer the RSA size
  // from OTBN.
  HARDENED_TRY(rsa_decrypt_finalize(hash_mode, label.data, label.len,
                                    plaintext.len, plaintext.data,
                                    plaintext_bytelen));

  // Consistency check; this should never happen.
  if (launder32(*plaintext_bytelen) > plaintext.len) {
    HARDENED_TRAP();
    return OTCRYPTO_FATAL_ERR;
  }
  HARDENED_CHECK_LE(*plaintext_bytelen, plaintext.len);

  return OTCRYPTO_OK;
}
