// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/include/ecc_p256.h"

#include "sw/device/lib/base/hardened_memory.h"
#include "sw/device/lib/crypto/drivers/entropy.h"
#include "sw/device/lib/crypto/drivers/hmac.h"
#include "sw/device/lib/crypto/impl/ecc/p256.h"
#include "sw/device/lib/crypto/impl/integrity.h"
#include "sw/device/lib/crypto/impl/keyblob.h"
#include "sw/device/lib/crypto/include/datatypes.h"

// Module ID for status codes.
#define MODULE_ID MAKE_MODULE_ID('p', '2', '5')

otcrypto_status_t otcrypto_ecdsa_p256_keygen(
    otcrypto_blinded_key_t *private_key, otcrypto_unblinded_key_t *public_key) {
  HARDENED_TRY(otcrypto_ecdsa_p256_keygen_async_start(private_key));
  return otcrypto_ecdsa_p256_keygen_async_finalize(private_key, public_key);
}

otcrypto_status_t otcrypto_ecdsa_p256_sign(
    const otcrypto_blinded_key_t *private_key,
    const otcrypto_hash_digest_t message_digest,
    otcrypto_word32_buf_t signature) {
  HARDENED_TRY(
      otcrypto_ecdsa_p256_sign_async_start(private_key, message_digest));
  return otcrypto_ecdsa_p256_sign_async_finalize(signature);
}

otcrypto_status_t otcrypto_ecdsa_p256_verify(
    const otcrypto_unblinded_key_t *public_key,
    const otcrypto_hash_digest_t message_digest,
    otcrypto_const_word32_buf_t signature,
    hardened_bool_t *verification_result) {
  HARDENED_TRY(otcrypto_ecdsa_p256_verify_async_start(
      public_key, message_digest, signature));
  return otcrypto_ecdsa_p256_verify_async_finalize(signature,
                                                   verification_result);
}

otcrypto_status_t otcrypto_ecdh_p256_keygen(
    otcrypto_blinded_key_t *private_key, otcrypto_unblinded_key_t *public_key) {
  HARDENED_TRY(otcrypto_ecdh_p256_keygen_async_start(private_key));
  return otcrypto_ecdh_p256_keygen_async_finalize(private_key, public_key);
}

otcrypto_status_t otcrypto_ecdh_p256(const otcrypto_blinded_key_t *private_key,
                                     const otcrypto_unblinded_key_t *public_key,
                                     otcrypto_blinded_key_t *shared_secret) {
  HARDENED_TRY(otcrypto_ecdh_p256_async_start(private_key, public_key));
  return otcrypto_ecdh_p256_async_finalize(shared_secret);
}

/**
 * Calls P-256 key generation.
 *
 * Can be used for both ECDSA and ECDH. If the key is hardware-backed, loads
 * the data from key manager and calls the sideloaded key generation routine.
 *
 * @param private_key Sideloaded key handle.
 * @return OK or error.
 */
OT_WARN_UNUSED_RESULT
static status_t internal_p256_keygen_start(
    const otcrypto_blinded_key_t *private_key) {
  // Ensure the entropy complex is initialized.
  HARDENED_TRY(entropy_complex_check());

  if (launder32(private_key->config.hw_backed) == kHardenedBoolTrue) {
    HARDENED_CHECK_EQ(private_key->config.hw_backed, kHardenedBoolTrue);
    HARDENED_TRY(keyblob_sideload_key_otbn(private_key));
    return p256_sideload_keygen_start();
  } else if (launder32(private_key->config.hw_backed) == kHardenedBoolFalse) {
    HARDENED_CHECK_EQ(private_key->config.hw_backed, kHardenedBoolFalse);
    return p256_keygen_start();
  } else {
    return OTCRYPTO_BAD_ARGS;
  }
  return OTCRYPTO_OK;
}

otcrypto_status_t otcrypto_ecdsa_p256_keygen_async_start(
    const otcrypto_blinded_key_t *private_key) {
  if (private_key == NULL || private_key->keyblob == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Check the key mode.
  if (launder32(private_key->config.key_mode) != kOtcryptoKeyModeEcdsaP256) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(private_key->config.key_mode, kOtcryptoKeyModeEcdsaP256);

  return internal_p256_keygen_start(private_key);
}

/**
 * Check the lengths of private keys for curve P-256.
 *
 * Checks the length of caller-allocated buffers for a P-256 private key. This
 * function may be used for both ECDSA and ECDH keys, since the key structure
 * is the same.
 *
 * If this check passes and `hw_backed` is false, it is safe to interpret
 * `private_key->keyblob` as a `p256_masked_scalar_t *`.
 *
 * @param private_key Private key struct to check.
 * @return OK if the lengths are correct or BAD_ARGS otherwise.
 */
OT_WARN_UNUSED_RESULT
static status_t p256_private_key_length_check(
    const otcrypto_blinded_key_t *private_key) {
  if (private_key->keyblob == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  if (launder32(private_key->config.hw_backed) == kHardenedBoolTrue) {
    // Skip the length check in this case; if the salt is the wrong length, the
    // keyblob library will catch it before we sideload the key.
    return OTCRYPTO_OK;
  }
  HARDENED_CHECK_NE(private_key->config.hw_backed, kHardenedBoolTrue);

  // Check the unmasked length.
  if (launder32(private_key->config.key_length) != kP256ScalarBytes) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(private_key->config.key_length, kP256ScalarBytes);

  // Check the single-share length.
  if (launder32(keyblob_share_num_words(private_key->config)) !=
      kP256MaskedScalarShareWords) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(keyblob_share_num_words(private_key->config),
                    kP256MaskedScalarShareWords);

  // Check the keyblob length.
  if (launder32(private_key->keyblob_length) != sizeof(p256_masked_scalar_t)) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(private_key->keyblob_length, sizeof(p256_masked_scalar_t));

  return OTCRYPTO_OK;
}

/**
 * Check the lengths of public keys for curve P-256.
 *
 * Checks the length of caller-allocated buffers for a P-256 public key. This
 * function may be used for both ECDSA and ECDH keys, since the key structure
 * is the same.
 *
 * If this check passes, it is safe to interpret public_key->key as a
 * `p256_point_t *`.
 *
 * @param public_key Public key struct to check.
 * @return OK if the lengths are correct or BAD_ARGS otherwise.
 */
OT_WARN_UNUSED_RESULT
static status_t p256_public_key_length_check(
    const otcrypto_unblinded_key_t *public_key) {
  if (launder32(public_key->key_length) != sizeof(p256_point_t)) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(public_key->key_length, sizeof(p256_point_t));
  return OTCRYPTO_OK;
}

/**
 * Finalize a keypair generation operation for curve P-256.
 *
 * This function assumes that space is already allocated for all key material
 * and that the length parameters on the structs are set accordingly, in the
 * same way as for `otcrypto_ecdh_p256_keygen_async_finalize` and
 * `otcrypto_ecdsa_p256_keygen_async_finalize`.
 *
 * @param[out] private_key Private key to populate.
 * @param[out] public_key Public key to populate.
 * @return OK or error.
 */
OT_WARN_UNUSED_RESULT
static status_t internal_p256_keygen_finalize(
    otcrypto_blinded_key_t *private_key, otcrypto_unblinded_key_t *public_key) {
  // Ensure the entropy complex is initialized.
  HARDENED_TRY(entropy_complex_check());

  // Check the lengths of caller-allocated buffers.
  HARDENED_TRY(p256_private_key_length_check(private_key));
  HARDENED_TRY(p256_public_key_length_check(public_key));
  p256_point_t *pk = (p256_point_t *)public_key->key;

  // Note: The `finalize` operations wipe DMEM after retrieving the keys, so if
  // an error occurs after this point then the keys would be unrecoverable.
  // The `finalize` call should be the last potentially error-causing line
  // before returning to the caller.

  if (launder32(private_key->config.hw_backed) == kHardenedBoolTrue) {
    HARDENED_CHECK_EQ(private_key->config.hw_backed, kHardenedBoolTrue);
    HARDENED_TRY(p256_sideload_keygen_finalize(pk));
  } else if (launder32(private_key->config.hw_backed) == kHardenedBoolFalse) {
    HARDENED_CHECK_EQ(private_key->config.hw_backed, kHardenedBoolFalse);

    // Randomize the keyblob before writing secret data.
    hardened_memshred(private_key->keyblob,
                      keyblob_num_words(private_key->config));

    p256_masked_scalar_t *sk = (p256_masked_scalar_t *)private_key->keyblob;
    HARDENED_TRY(p256_keygen_finalize(sk, pk));
  } else {
    return OTCRYPTO_BAD_ARGS;
  }

  // Set the key checksums.
  private_key->checksum = integrity_blinded_checksum(private_key);
  public_key->checksum = integrity_unblinded_checksum(public_key);

  // Clear the OTBN sideload slot (in case the seed was sideloaded).
  return keymgr_sideload_clear_otbn();
}

otcrypto_status_t otcrypto_ecdsa_p256_keygen_async_finalize(
    otcrypto_blinded_key_t *private_key, otcrypto_unblinded_key_t *public_key) {
  // Check for any NULL pointers.
  if (private_key == NULL || public_key == NULL ||
      private_key->keyblob == NULL || public_key->key == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Check the key modes.
  if (launder32(private_key->config.key_mode) != kOtcryptoKeyModeEcdsaP256 ||
      launder32(public_key->key_mode) != kOtcryptoKeyModeEcdsaP256) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(private_key->config.key_mode, kOtcryptoKeyModeEcdsaP256);
  HARDENED_CHECK_EQ(public_key->key_mode, kOtcryptoKeyModeEcdsaP256);

  return internal_p256_keygen_finalize(private_key, public_key);
}

otcrypto_status_t otcrypto_ecdsa_p256_sign_async_start(
    const otcrypto_blinded_key_t *private_key,
    const otcrypto_hash_digest_t message_digest) {
  if (private_key == NULL || private_key->keyblob == NULL ||
      message_digest.data == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Check that the entropy complex is initialized.
  HARDENED_TRY(entropy_complex_check());

  // Check the integrity of the private key.
  if (launder32(integrity_blinded_key_check(private_key)) !=
      kHardenedBoolTrue) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(integrity_blinded_key_check(private_key),
                    kHardenedBoolTrue);

  if (launder32(private_key->config.key_mode) != kOtcryptoKeyModeEcdsaP256) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(private_key->config.key_mode, kOtcryptoKeyModeEcdsaP256);

  // Check the digest length.
  if (launder32(message_digest.len) != kP256ScalarWords) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(message_digest.len, kP256ScalarWords);

  // Check the key length.
  HARDENED_TRY(p256_private_key_length_check(private_key));

  if (launder32(private_key->config.hw_backed) == kHardenedBoolFalse) {
    // Start the asynchronous signature-generation routine.
    HARDENED_CHECK_EQ(private_key->config.hw_backed, kHardenedBoolFalse);
    p256_masked_scalar_t *sk = (p256_masked_scalar_t *)private_key->keyblob;
    return p256_ecdsa_sign_start(message_digest.data, sk);
  } else if (launder32(private_key->config.hw_backed) == kHardenedBoolTrue) {
    // Load the key and start in sideloaded-key mode.
    HARDENED_CHECK_EQ(private_key->config.hw_backed, kHardenedBoolTrue);
    HARDENED_TRY(keyblob_sideload_key_otbn(private_key));
    return p256_ecdsa_sideload_sign_start(message_digest.data);
  }

  // Invalid value for private_key->hw_backed.
  return OTCRYPTO_BAD_ARGS;
}

/**
 * Check the length of a signature buffer for ECDSA with P-256.
 *
 * If this check passes on `signature.len`, it is safe to interpret
 * `signature.data` as `p256_ecdsa_signature_t *`.
 *
 * @param len Length to check.
 * @return OK if the lengths are correct or BAD_ARGS otherwise.
 */
OT_WARN_UNUSED_RESULT
static status_t p256_signature_length_check(size_t len) {
  if (launder32(len) > UINT32_MAX / sizeof(uint32_t) ||
      launder32(len) * sizeof(uint32_t) != sizeof(p256_ecdsa_signature_t)) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(len * sizeof(uint32_t), sizeof(p256_ecdsa_signature_t));

  return OTCRYPTO_OK;
}

otcrypto_status_t otcrypto_ecdsa_p256_sign_async_finalize(
    otcrypto_word32_buf_t signature) {
  if (signature.data == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Ensure the entropy complex is initialized.
  HARDENED_TRY(entropy_complex_check());

  HARDENED_TRY(p256_signature_length_check(signature.len));
  p256_ecdsa_signature_t *sig_p256 = (p256_ecdsa_signature_t *)signature.data;
  // Note: This operation wipes DMEM, so if an error occurs after this
  // point then the signature would be unrecoverable. This should be the
  // last potentially error-causing line before returning to the caller.
  HARDENED_TRY(p256_ecdsa_sign_finalize(sig_p256));

  // Clear the OTBN sideload slot (in case the key was sideloaded).
  return keymgr_sideload_clear_otbn();
}

otcrypto_status_t otcrypto_ecdsa_p256_verify_async_start(
    const otcrypto_unblinded_key_t *public_key,
    const otcrypto_hash_digest_t message_digest,
    otcrypto_const_word32_buf_t signature) {
  if (public_key == NULL || signature.data == NULL ||
      message_digest.data == NULL || public_key->key == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Ensure the entropy complex is initialized.
  HARDENED_TRY(entropy_complex_check());

  // Check the integrity of the public key.
  if (launder32(integrity_unblinded_key_check(public_key)) !=
      kHardenedBoolTrue) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(integrity_unblinded_key_check(public_key),
                    kHardenedBoolTrue);

  // Check the public key mode.
  if (launder32(public_key->key_mode) != kOtcryptoKeyModeEcdsaP256) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(public_key->key_mode, kOtcryptoKeyModeEcdsaP256);

  // Check the public key size.
  HARDENED_TRY(p256_public_key_length_check(public_key));
  p256_point_t *pk = (p256_point_t *)public_key->key;

  // Check the digest length.
  if (launder32(message_digest.len) != kP256ScalarWords) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(message_digest.len, kP256ScalarWords);

  // Check the signature lengths.
  HARDENED_TRY(p256_signature_length_check(signature.len));
  p256_ecdsa_signature_t *sig = (p256_ecdsa_signature_t *)signature.data;

  // Start the asynchronous signature-verification routine.
  return p256_ecdsa_verify_start(sig, message_digest.data, pk);
}

otcrypto_status_t otcrypto_ecdsa_p256_verify_async_finalize(
    otcrypto_const_word32_buf_t signature,
    hardened_bool_t *verification_result) {
  if (verification_result == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Ensure the entropy complex is initialized.
  HARDENED_TRY(entropy_complex_check());

  HARDENED_TRY(p256_signature_length_check(signature.len));
  p256_ecdsa_signature_t *sig_p256 = (p256_ecdsa_signature_t *)signature.data;
  return p256_ecdsa_verify_finalize(sig_p256, verification_result);
}

otcrypto_status_t otcrypto_ecdh_p256_keygen_async_start(
    const otcrypto_blinded_key_t *private_key) {
  if (private_key == NULL || private_key->keyblob == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  if (launder32(private_key->config.key_mode) != kOtcryptoKeyModeEcdhP256) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(private_key->config.key_mode, kOtcryptoKeyModeEcdhP256);
  return internal_p256_keygen_start(private_key);
}

otcrypto_status_t otcrypto_ecdh_p256_keygen_async_finalize(
    otcrypto_blinded_key_t *private_key, otcrypto_unblinded_key_t *public_key) {
  // Check for any NULL pointers.
  if (private_key == NULL || public_key == NULL ||
      private_key->keyblob == NULL || public_key->key == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  if (launder32(public_key->key_mode) != kOtcryptoKeyModeEcdhP256 ||
      launder32(private_key->config.key_mode) != kOtcryptoKeyModeEcdhP256) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(public_key->key_mode, kOtcryptoKeyModeEcdhP256);
  HARDENED_CHECK_EQ(private_key->config.key_mode, kOtcryptoKeyModeEcdhP256);
  return internal_p256_keygen_finalize(private_key, public_key);
}

otcrypto_status_t otcrypto_ecdh_p256_async_start(
    const otcrypto_blinded_key_t *private_key,
    const otcrypto_unblinded_key_t *public_key) {
  if (private_key == NULL || public_key == NULL || public_key->key == NULL ||
      private_key->keyblob == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Ensure the entropy complex is initialized.
  HARDENED_TRY(entropy_complex_check());

  // Check the integrity of the keys.
  if (launder32(integrity_blinded_key_check(private_key)) !=
          kHardenedBoolTrue ||
      launder32(integrity_unblinded_key_check(public_key)) !=
          kHardenedBoolTrue) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(integrity_blinded_key_check(private_key),
                    kHardenedBoolTrue);
  HARDENED_CHECK_EQ(integrity_unblinded_key_check(public_key),
                    kHardenedBoolTrue);

  // Check the key modes.
  if (launder32(private_key->config.key_mode) != kOtcryptoKeyModeEcdhP256 ||
      launder32(public_key->key_mode) != kOtcryptoKeyModeEcdhP256) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(private_key->config.key_mode, kOtcryptoKeyModeEcdhP256);
  HARDENED_CHECK_EQ(public_key->key_mode, kOtcryptoKeyModeEcdhP256);

  // Check the key lengths.
  HARDENED_TRY(p256_private_key_length_check(private_key));
  HARDENED_TRY(p256_public_key_length_check(public_key));
  p256_point_t *pk = (p256_point_t *)public_key->key;

  if (launder32(private_key->config.hw_backed) == kHardenedBoolTrue) {
    HARDENED_CHECK_EQ(private_key->config.hw_backed, kHardenedBoolTrue);
    HARDENED_TRY(keyblob_sideload_key_otbn(private_key));
    return p256_sideload_ecdh_start(pk);
  } else if (launder32(private_key->config.hw_backed) == kHardenedBoolFalse) {
    HARDENED_CHECK_EQ(private_key->config.hw_backed, kHardenedBoolFalse);
    p256_masked_scalar_t *sk = (p256_masked_scalar_t *)private_key->keyblob;
    return p256_ecdh_start(sk, pk);
  }

  // Invalid value for `hw_backed`.
  return OTCRYPTO_BAD_ARGS;
}

otcrypto_status_t otcrypto_ecdh_p256_async_finalize(
    otcrypto_blinded_key_t *shared_secret) {
  if (shared_secret == NULL || shared_secret->keyblob == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Ensure the entropy complex is initialized.
  HARDENED_TRY(entropy_complex_check());

  // Shared keys cannot be sideloaded because they are software-generated.
  if (launder32(shared_secret->config.hw_backed) != kHardenedBoolFalse) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(shared_secret->config.hw_backed, kHardenedBoolFalse);

  // Check shared secret length.
  if (launder32(shared_secret->config.key_length) != kP256CoordBytes) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(shared_secret->config.key_length, kP256CoordBytes);
  if (launder32(shared_secret->keyblob_length) !=
      keyblob_num_words(shared_secret->config) * sizeof(uint32_t)) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(
      shared_secret->keyblob_length,
      keyblob_num_words(shared_secret->config) * sizeof(uint32_t));

  // Note: This operation wipes DMEM after retrieving the keys, so if an error
  // occurs after this point then the keys would be unrecoverable. This should
  // be the last potentially error-causing line before returning to the caller.
  p256_ecdh_shared_key_t ss;
  hardened_memshred(ss.share0, ARRAYSIZE(ss.share0));
  hardened_memshred(ss.share1, ARRAYSIZE(ss.share1));
  HARDENED_TRY(p256_ecdh_finalize(&ss));

  HARDENED_TRY(keyblob_from_shares(ss.share0, ss.share1, shared_secret->config,
                                   shared_secret->keyblob));

  // Set the checksum.
  shared_secret->checksum = integrity_blinded_checksum(shared_secret);

  // Clear the OTBN sideload slot (in case the seed was sideloaded).
  return keymgr_sideload_clear_otbn();
}
