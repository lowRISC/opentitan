// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/include/ecc_p384.h"

#include "sw/device/lib/base/hardened_memory.h"
#include "sw/device/lib/crypto/drivers/hmac.h"
#include "sw/device/lib/crypto/impl/ecc/p384.h"
#include "sw/device/lib/crypto/impl/keyblob.h"
#include "sw/device/lib/crypto/include/config.h"
#include "sw/device/lib/crypto/include/datatypes.h"
#include "sw/device/lib/crypto/include/integrity.h"

// Module ID for status codes.
#define MODULE_ID MAKE_MODULE_ID('p', '3', '8')

/**
 * Calls P-384 key generation.
 *
 * Can be used for both ECDSA and ECDH. If the key is hardware-backed, loads
 * the data from key manager and calls the sideloaded key generation routine.
 *
 * @param private_key Sideloaded key handle.
 * @return OK or error.
 */
OT_WARN_UNUSED_RESULT
static status_t internal_p384_keygen_start(
    const otcrypto_blinded_key_t *private_key) {
  if (private_key->config.hw_backed == kHardenedBoolTrue) {
    HARDENED_CHECK_EQ(launder32(private_key->config.hw_backed),
                      kHardenedBoolTrue);
    HARDENED_TRY(keyblob_sideload_key_otbn(private_key));
    return p384_sideload_keygen_start();
  } else if (private_key->config.hw_backed == kHardenedBoolFalse) {
    HARDENED_CHECK_EQ(launder32(private_key->config.hw_backed),
                      kHardenedBoolFalse);
    return p384_keygen_start();
  } else {
    return OTCRYPTO_BAD_ARGS;
  }
  return OTCRYPTO_OK;
}

otcrypto_status_t otcrypto_ecdsa_p384_keygen_async_start(
    const otcrypto_blinded_key_t *private_key) {
  if (private_key == NULL || private_key->keyblob == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Check the key mode.
  if (private_key->config.key_mode != kOtcryptoKeyModeEcdsaP384) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(launder32(private_key->config.key_mode),
                    kOtcryptoKeyModeEcdsaP384);

  HARDENED_TRY_WIPE_DMEM(internal_p384_keygen_start(private_key));
  return otcrypto_eval_exit(OTCRYPTO_OK);
}

/**
 * Check the lengths of private keys for curve P-384.
 *
 * Checks the length of caller-allocated buffers for a P-384 private key. This
 * function may be used for both ECDSA and ECDH keys, since the key structure
 * is the same.
 *
 * If this check passes and `hw_backed` is false, it is safe to interpret
 * `private_key->keyblob` as a `p384_masked_scalar_t *`.
 *
 * @param private_key Private key struct to check.
 * @return OK if the lengths are correct or BAD_ARGS otherwise.
 */
OT_WARN_UNUSED_RESULT
static status_t p384_private_key_length_check(
    const otcrypto_blinded_key_t *private_key) {
  if (private_key->keyblob == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  if (private_key->config.hw_backed == kHardenedBoolTrue) {
    // Skip the length check in this case; if the salt is the wrong length, the
    // keyblob library will catch it before we sideload the key.
    return OTCRYPTO_OK;
  }
  HARDENED_CHECK_NE(launder32(private_key->config.hw_backed),
                    kHardenedBoolTrue);

  // Check the unmasked length.
  if (private_key->config.key_length != kP384ScalarBytes) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(launder32(private_key->config.key_length),
                    kP384ScalarBytes);

  // Check the single-share length.
  if (keyblob_share_num_words(private_key->config) !=
      kP384MaskedScalarShareWords) {
    // COVERAGE (MISSING) We do not cover bad share length inputs
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(launder32(keyblob_share_num_words(private_key->config)),
                    kP384MaskedScalarShareWords);

  // Check the keyblob length.
  if (private_key->keyblob_length != kP384MaskedScalarTotalShareBytes) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(launder32(private_key->keyblob_length),
                    kP384MaskedScalarTotalShareBytes);

  return OTCRYPTO_OK;
}

/**
 * Check the lengths of public keys for curve P-384.
 *
 * Checks the length of caller-allocated buffers for a P-384 public key. This
 * function may be used for both ECDSA and ECDH keys, since the key structure
 * is the same.
 *
 * If this check passes, it is safe to interpret public_key->key as a
 * `p384_point_t *`.
 *
 * @param public_key Public key struct to check.
 * @return OK if the lengths are correct or BAD_ARGS otherwise.
 */
OT_WARN_UNUSED_RESULT
static status_t p384_public_key_length_check(
    const otcrypto_unblinded_key_t *public_key) {
  if (public_key->key_length != sizeof(p384_point_t)) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(launder32(public_key->key_length), sizeof(p384_point_t));
  return OTCRYPTO_OK;
}
/**
 * Finalize a keypair generation operation for curve P-384.
 *
 * This function assumes that space is already allocated for all key material
 * and that the length parameters on the structs are set accordingly, in the
 * same way as for `otcrypto_ecdh_p384_keygen_async_finalize` and
 * `otcrypto_ecdsa_p384_keygen_async_finalize`.
 *
 * @param[out] private_key Private key to populate.
 * @param[out] public_key Public key to populate.
 * @return OK or error.
 */
OT_WARN_UNUSED_RESULT
static status_t internal_p384_keygen_finalize(
    otcrypto_blinded_key_t *private_key, otcrypto_unblinded_key_t *public_key) {
  // Check the lengths of caller-allocated buffers.
  HARDENED_TRY(p384_private_key_length_check(private_key));
  HARDENED_TRY(p384_public_key_length_check(public_key));

  // Interpret the key buffer as a P-384 point.
  p384_point_t *pk = (p384_point_t *)public_key->key;

  if (private_key->config.hw_backed == kHardenedBoolTrue) {
    // Note: This operation wipes DMEM after retrieving the keys, so if an error
    // occurs after this point then the keys would be unrecoverable. This should
    // be the last potentially error-causing line before returning to the
    // caller.
    HARDENED_CHECK_EQ(launder32(private_key->config.hw_backed),
                      kHardenedBoolTrue);
    HARDENED_TRY(p384_sideload_keygen_finalize(pk));
  } else if (private_key->config.hw_backed == kHardenedBoolFalse) {
    HARDENED_CHECK_EQ(launder32(private_key->config.hw_backed),
                      kHardenedBoolFalse);

    // Randomize the keyblob before writing secret data.
    HARDENED_TRY(hardened_memshred(private_key->keyblob,
                                   keyblob_num_words(private_key->config)));

    // Note: This operation wipes DMEM after retrieving the keys, so if an error
    // occurs after this point then the keys would be unrecoverable. This should
    // be the last potentially error-causing line before returning to the
    // caller.
    p384_masked_scalar_t private_scalar;
    HARDENED_TRY(p384_keygen_finalize(&private_scalar, pk));
    HARDENED_CHECK_EQ(p384_masked_scalar_checksum_check(&private_scalar),
                      kHardenedBoolTrue);
    HARDENED_TRY(hardened_memcpy(private_key->keyblob, private_scalar.share0,
                                 kP384MaskedScalarTotalShareWords));
    HARDENED_CHECK_EQ(
        hardened_memeq(private_scalar.share0, private_key->keyblob,
                       kP384MaskedScalarTotalShareWords),
        kHardenedBoolTrue);
  } else {
    return OTCRYPTO_BAD_ARGS;
  }

  private_key->checksum = integrity_blinded_checksum(private_key);
  public_key->checksum = integrity_unblinded_checksum(public_key);
  return OTCRYPTO_OK;
}

/**
 * Check the length of a signature buffer for ECDSA with P-384.
 *
 * If this check passes on `signature.len`, it is safe to interpret
 * `signature.data` as `p384_ecdsa_signature_t *`.
 *
 * @param len Length to check.
 * @return OK if the lengths are correct or BAD_ARGS otherwise.
 */
OT_WARN_UNUSED_RESULT
static status_t p384_signature_length_check(size_t len) {
  if (len > UINT32_MAX / sizeof(uint32_t) ||
      len * sizeof(uint32_t) != sizeof(p384_ecdsa_signature_t)) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(launder32(len) * sizeof(uint32_t),
                    sizeof(p384_ecdsa_signature_t));

  return OTCRYPTO_OK;
}

otcrypto_status_t otcrypto_ecdsa_p384_keygen(
    otcrypto_blinded_key_t *private_key, otcrypto_unblinded_key_t *public_key) {
  HARDENED_TRY(otcrypto_ecdsa_p384_keygen_async_start(private_key));
  return otcrypto_ecdsa_p384_keygen_async_finalize(private_key, public_key);
}

otcrypto_status_t otcrypto_ecdsa_p384_sign_config_k(
    const otcrypto_blinded_key_t *private_key,
    const otcrypto_blinded_key_t *secret_scalar,
    const otcrypto_hash_digest_t message_digest,
    otcrypto_word32_buf_t *signature) {
  HARDENED_TRY(otcrypto_ecdsa_p384_sign_config_k_async_start(
      private_key, secret_scalar, message_digest));
  return otcrypto_ecdsa_p384_sign_async_finalize(signature);
}

otcrypto_status_t otcrypto_ecdsa_p384_sign(
    const otcrypto_blinded_key_t *private_key,
    const otcrypto_hash_digest_t message_digest,
    otcrypto_word32_buf_t *signature) {
  HARDENED_TRY(
      otcrypto_ecdsa_p384_sign_async_start(private_key, message_digest));
  return otcrypto_ecdsa_p384_sign_async_finalize(signature);
}

otcrypto_status_t otcrypto_ecdsa_p384_verify(
    const otcrypto_unblinded_key_t *public_key,
    const otcrypto_hash_digest_t message_digest,
    const otcrypto_const_word32_buf_t *signature,
    hardened_bool_t *verification_result) {
  HARDENED_TRY(otcrypto_ecdsa_p384_verify_async_start(
      public_key, message_digest, signature));
  return otcrypto_ecdsa_p384_verify_async_finalize(signature,
                                                   verification_result);
}

otcrypto_status_t otcrypto_ecdsa_p384_sign_verify(
    const otcrypto_blinded_key_t *private_key,
    const otcrypto_unblinded_key_t *public_key,
    const otcrypto_hash_digest_t message_digest,
    otcrypto_word32_buf_t *signature) {
  // Signature generation.
  HARDENED_TRY(
      otcrypto_ecdsa_p384_sign(private_key, message_digest, signature));

  // Verify signature before releasing it.
  otcrypto_const_word32_buf_t signature_check = OTCRYPTO_MAKE_BUF(
      otcrypto_const_word32_buf_t, signature->data, signature->len);
  hardened_bool_t verification_result = kHardenedBoolFalse;
  HARDENED_TRY(otcrypto_ecdsa_p384_verify(
      public_key, message_digest, &signature_check, &verification_result));

  // Trap if signature verification failed.
  HARDENED_CHECK_EQ(verification_result, kHardenedBoolTrue);
  return OTCRYPTO_OK;
}

otcrypto_status_t otcrypto_ecdh_p384_keygen(
    otcrypto_blinded_key_t *private_key, otcrypto_unblinded_key_t *public_key) {
  HARDENED_TRY(otcrypto_ecdh_p384_keygen_async_start(private_key));
  return otcrypto_ecdh_p384_keygen_async_finalize(private_key, public_key);
}

otcrypto_status_t otcrypto_ecdh_p384(const otcrypto_blinded_key_t *private_key,
                                     const otcrypto_unblinded_key_t *public_key,
                                     otcrypto_blinded_key_t *shared_secret) {
  HARDENED_TRY(otcrypto_ecdh_p384_async_start(private_key, public_key));
  return otcrypto_ecdh_p384_async_finalize(shared_secret);
}

otcrypto_status_t otcrypto_ecc_p384_point_on_curve(
    const otcrypto_unblinded_key_t *point, hardened_bool_t *check_result) {
  if (point == NULL || point->key == NULL || check_result == NULL) {
    // COVERAGE (MISSING) We do not cover null inputs
    return OTCRYPTO_BAD_ARGS;
  }

  p384_point_t *pt = (p384_point_t *)point->key;
  HARDENED_TRY(p384_point_on_curve_check(pt, check_result));

  return otcrypto_eval_exit(OTCRYPTO_OK);
}

status_t otcrypto_ecc_p384_base_point_mult(
    const otcrypto_blinded_key_t *private_key,
    otcrypto_unblinded_key_t *public_key) {
  if (private_key == NULL || public_key == NULL) {
    // COVERAGE (MISSING) We do not cover null inputs
    return OTCRYPTO_BAD_ARGS;
  }

  HARDENED_CHECK_EQ(integrity_blinded_key_check(private_key),
                    kHardenedBoolTrue);

  p384_masked_scalar_t private_scalar;
  HARDENED_TRY(hardened_memcpy(private_scalar.share0, private_key->keyblob,
                               kP384MaskedScalarTotalShareWords));
  HARDENED_CHECK_EQ(hardened_memeq(private_key->keyblob, private_scalar.share0,
                                   kP384MaskedScalarTotalShareWords),
                    kHardenedBoolTrue);
  private_scalar.checksum = p384_masked_scalar_checksum(&private_scalar);

  p384_point_t *pk = (p384_point_t *)public_key->key;
  HARDENED_TRY_WIPE_DMEM(p384_base_point_mult(&private_scalar, pk));

  public_key->checksum = integrity_unblinded_checksum(public_key);

  return OTCRYPTO_OK;
}

otcrypto_status_t otcrypto_ecdsa_p384_keygen_async_finalize(
    otcrypto_blinded_key_t *private_key, otcrypto_unblinded_key_t *public_key) {
  // Check for any NULL pointers.
  if (private_key == NULL || public_key == NULL ||
      private_key->keyblob == NULL || public_key->key == NULL) {
    // COVERAGE (MISSING) We do not cover null inputs.
    return OTCRYPTO_BAD_ARGS;
  }

  // Check the key modes.
  if (private_key->config.key_mode != kOtcryptoKeyModeEcdsaP384 ||
      public_key->key_mode != kOtcryptoKeyModeEcdsaP384) {
    // COVERAGE (MISSING) We do not cover bad key mode inputs.
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(launder32(private_key->config.key_mode),
                    kOtcryptoKeyModeEcdsaP384);
  HARDENED_CHECK_EQ(launder32(public_key->key_mode), kOtcryptoKeyModeEcdsaP384);

  HARDENED_TRY_WIPE_DMEM(
      internal_p384_keygen_finalize(private_key, public_key));

  // Clear the OTBN sideload slot (in case the seed was sideloaded).
  return otcrypto_eval_exit(keymgr_sideload_clear_otbn());
}

static otcrypto_status_t otcrypto_ecdsa_p384_sign_async_start_setup(
    const otcrypto_blinded_key_t *private_key,
    const otcrypto_hash_digest_t message_digest) {
  if (private_key == NULL || private_key->keyblob == NULL ||
      message_digest.data == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Check the integrity of the private key.
  if (integrity_blinded_key_check(private_key) != kHardenedBoolTrue) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(launder32(integrity_blinded_key_check(private_key)),
                    kHardenedBoolTrue);

  if (private_key->config.key_mode != kOtcryptoKeyModeEcdsaP384) {
    // COVERAGE (MISSING) We do not cover bad key mode inputs.
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(launder32(private_key->config.key_mode),
                    kOtcryptoKeyModeEcdsaP384);

  // Check the digest length.
  if (message_digest.len != kP384ScalarWords) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(launder32(message_digest.len), kP384ScalarWords);

  // Check the key length.
  HARDENED_TRY(p384_private_key_length_check(private_key));

  return OTCRYPTO_OK;
}

otcrypto_status_t otcrypto_ecdsa_p384_sign_config_k_async_start(
    const otcrypto_blinded_key_t *private_key,
    const otcrypto_blinded_key_t *secret_scalar,
    const otcrypto_hash_digest_t message_digest) {
  // Do initial checks on the private key and digest.
  HARDENED_TRY(
      otcrypto_ecdsa_p384_sign_async_start_setup(private_key, message_digest));

  // Load the secret key d.
  HARDENED_CHECK_EQ(launder32(private_key->config.hw_backed),
                    kHardenedBoolFalse);
  p384_masked_scalar_t private_scalar;
  HARDENED_TRY(hardened_memcpy(private_scalar.share0, private_key->keyblob,
                               kP384MaskedScalarTotalShareWords));
  private_scalar.checksum = p384_masked_scalar_checksum(&private_scalar);

  // Load the secret scalar k.
  // The use of fixed scalars should be limited to KATs.
  HARDENED_CHECK_EQ(launder32(secret_scalar->config.hw_backed),
                    kHardenedBoolFalse);
  p384_masked_scalar_t config_k_scalar;
  HARDENED_TRY(hardened_memcpy(config_k_scalar.share0, secret_scalar->keyblob,
                               kP384MaskedScalarTotalShareWords));
  config_k_scalar.checksum = p384_masked_scalar_checksum(&config_k_scalar);
  HARDENED_TRY_WIPE_DMEM(p384_ecdsa_sign_config_k_start(
      message_digest.data, &private_scalar, &config_k_scalar));

  // To detect forgeries of the pointer to the private key that we have passed
  // to the ECC implementation, check again its integrity. If the pointer would
  // have been tampered with between the first integrity check we did when
  // entering the CryptoLib and here, we would detect this now.
  HARDENED_CHECK_EQ(integrity_blinded_key_check(private_key),
                    kHardenedBoolTrue);

  return otcrypto_eval_exit(OTCRYPTO_OK);
}

otcrypto_status_t otcrypto_ecdsa_p384_sign_async_start(
    const otcrypto_blinded_key_t *private_key,
    const otcrypto_hash_digest_t message_digest) {
  // Do initial checks on the private key and digest.
  HARDENED_TRY(
      otcrypto_ecdsa_p384_sign_async_start_setup(private_key, message_digest));

  // Load the secret key d.
  if (private_key->config.hw_backed == kHardenedBoolFalse) {
    // Start the asynchronous signature-generation routine.
    HARDENED_CHECK_EQ(launder32(private_key->config.hw_backed),
                      kHardenedBoolFalse);
    p384_masked_scalar_t private_scalar;
    HARDENED_TRY(hardened_memcpy(private_scalar.share0, private_key->keyblob,
                                 kP384MaskedScalarTotalShareWords));
    HARDENED_CHECK_EQ(
        hardened_memeq(private_key->keyblob, private_scalar.share0,
                       kP384MaskedScalarTotalShareWords),
        kHardenedBoolTrue);
    private_scalar.checksum = p384_masked_scalar_checksum(&private_scalar);
    HARDENED_TRY_WIPE_DMEM(
        p384_ecdsa_sign_start(message_digest.data, &private_scalar));
  } else if (private_key->config.hw_backed == kHardenedBoolTrue) {
    // Load the key and start in sideloaded-key mode.
    HARDENED_CHECK_EQ(launder32(private_key->config.hw_backed),
                      kHardenedBoolTrue);
    HARDENED_TRY_WIPE_DMEM(keyblob_sideload_key_otbn(private_key));
    HARDENED_TRY_WIPE_DMEM(p384_ecdsa_sideload_sign_start(message_digest.data));
  } else {
    // Invalid value for private_key->hw_backed.
    // COVERAGE (MISSING) We do not cover bad hw_backed inputs.
    return OTCRYPTO_BAD_ARGS;
  }

  // To detect forgeries of the pointer to the private key that we have passed
  // to the ECC implementation, check again its integrity. If the pointer would
  // have been tampered with between the first integrity check we did when
  // entering the CryptoLib and here, we would detect this now.
  HARDENED_CHECK_EQ(integrity_blinded_key_check(private_key),
                    kHardenedBoolTrue);

  return otcrypto_eval_exit(OTCRYPTO_OK);
}

otcrypto_status_t otcrypto_ecdsa_p384_sign_async_finalize(
    otcrypto_word32_buf_t *signature) {
  if (signature->data == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Verify the input buffer
  HARDENED_CHECK_EQ(kHardenedBoolTrue, OTCRYPTO_CHECK_BUF(signature));

  HARDENED_TRY(p384_signature_length_check(signature->len));
  p384_ecdsa_signature_t *sig_p384 = (p384_ecdsa_signature_t *)signature->data;
  // Note: This operation wipes DMEM, so if an error occurs after this
  // point then the signature would be unrecoverable. This should be the
  // last potentially error-causing line before returning to the caller.
  HARDENED_TRY_WIPE_DMEM(p384_ecdsa_sign_finalize(sig_p384));

  // Clear the OTBN sideload slot (in case the key was sideloaded).
  return otcrypto_eval_exit(keymgr_sideload_clear_otbn());
}
otcrypto_status_t otcrypto_ecdsa_p384_verify_async_start(
    const otcrypto_unblinded_key_t *public_key,
    const otcrypto_hash_digest_t message_digest,
    const otcrypto_const_word32_buf_t *signature) {
  if (public_key == NULL || signature->data == NULL ||
      message_digest.data == NULL || public_key->key == NULL) {
    // COVERAGE (MISSING) We do not cover null inputs.
    return OTCRYPTO_BAD_ARGS;
  }

  // Check the integrity of the public key.
  if (integrity_unblinded_key_check(public_key) != kHardenedBoolTrue) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(launder32(integrity_unblinded_key_check(public_key)),
                    kHardenedBoolTrue);

  // Check the public key mode.
  if (public_key->key_mode != kOtcryptoKeyModeEcdsaP384) {
    // COVERAGE (MISSING) We do not cover bad key mode inputs.
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(launder32(public_key->key_mode), kOtcryptoKeyModeEcdsaP384);

  // Check the public key size.
  HARDENED_TRY(p384_public_key_length_check(public_key));
  p384_point_t *pk = (p384_point_t *)public_key->key;

  // Check the digest length.
  if (message_digest.len != kP384ScalarWords) {
    // COVERAGE (MISSING) We do not cover bad length inputs.
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(launder32(message_digest.len), kP384ScalarWords);

  // Check the signature lengths.
  HARDENED_TRY(p384_signature_length_check(signature->len));
  p384_ecdsa_signature_t *sig = (p384_ecdsa_signature_t *)signature->data;

  // Start the asynchronous signature-verification routine.
  HARDENED_TRY_WIPE_DMEM(p384_ecdsa_verify_start(sig, message_digest.data, pk));

  // To detect forgeries of the pointer to the public key that we have passed
  // to the ECC implementation, check again its integrity. If the pointer would
  // have been tampered with between the first integrity check we did when
  // entering the CryptoLib and here, we would detect this now.
  HARDENED_CHECK_EQ(integrity_unblinded_key_check(public_key),
                    kHardenedBoolTrue);
  return otcrypto_eval_exit(OTCRYPTO_OK);
}

otcrypto_status_t otcrypto_ecdsa_p384_verify_async_finalize(
    const otcrypto_const_word32_buf_t *signature,
    hardened_bool_t *verification_result) {
  if (verification_result == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Verify the input buffer
  HARDENED_CHECK_EQ(kHardenedBoolTrue, OTCRYPTO_CHECK_BUF(signature));

  HARDENED_TRY(p384_signature_length_check(signature->len));
  p384_ecdsa_signature_t *sig_p384 = (p384_ecdsa_signature_t *)signature->data;

  HARDENED_TRY_WIPE_DMEM(
      p384_ecdsa_verify_finalize(sig_p384, verification_result));

  return otcrypto_eval_exit(OTCRYPTO_OK);
}

otcrypto_status_t otcrypto_ecdh_p384_keygen_async_start(
    const otcrypto_blinded_key_t *private_key) {
  if (private_key == NULL || private_key->keyblob == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  if (private_key->config.key_mode != kOtcryptoKeyModeEcdhP384) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(launder32(private_key->config.key_mode),
                    kOtcryptoKeyModeEcdhP384);
  HARDENED_TRY_WIPE_DMEM(internal_p384_keygen_start(private_key));
  return otcrypto_eval_exit(OTCRYPTO_OK);
}

otcrypto_status_t otcrypto_ecdh_p384_keygen_async_finalize(
    otcrypto_blinded_key_t *private_key, otcrypto_unblinded_key_t *public_key) {
  // Check for any NULL pointers.
  if (private_key == NULL || public_key == NULL ||
      private_key->keyblob == NULL || public_key->key == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  if (public_key->key_mode != kOtcryptoKeyModeEcdhP384 ||
      private_key->config.key_mode != kOtcryptoKeyModeEcdhP384) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(launder32(public_key->key_mode), kOtcryptoKeyModeEcdhP384);
  HARDENED_CHECK_EQ(launder32(private_key->config.key_mode),
                    kOtcryptoKeyModeEcdhP384);
  HARDENED_TRY_WIPE_DMEM(
      internal_p384_keygen_finalize(private_key, public_key));
  return otcrypto_eval_exit(OTCRYPTO_OK);
}

otcrypto_status_t otcrypto_ecdh_p384_async_start(
    const otcrypto_blinded_key_t *private_key,
    const otcrypto_unblinded_key_t *public_key) {
  if (private_key == NULL || public_key == NULL || public_key->key == NULL ||
      private_key->keyblob == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Check the integrity of the keys.
  if (integrity_blinded_key_check(private_key) != kHardenedBoolTrue ||
      integrity_unblinded_key_check(public_key) != kHardenedBoolTrue) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(launder32(integrity_blinded_key_check(private_key)),
                    kHardenedBoolTrue);
  HARDENED_CHECK_EQ(launder32(integrity_unblinded_key_check(public_key)),
                    kHardenedBoolTrue);

  // Check the key modes.
  if (private_key->config.key_mode != kOtcryptoKeyModeEcdhP384 ||
      public_key->key_mode != kOtcryptoKeyModeEcdhP384) {
    // COVERAGE (MISSING) We do not cover bad key mode inputs.
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(launder32(private_key->config.key_mode),
                    kOtcryptoKeyModeEcdhP384);
  HARDENED_CHECK_EQ(launder32(public_key->key_mode), kOtcryptoKeyModeEcdhP384);

  // Check the key lengths.
  HARDENED_TRY(p384_private_key_length_check(private_key));
  HARDENED_TRY(p384_public_key_length_check(public_key));
  p384_point_t *pk = (p384_point_t *)public_key->key;

  if (private_key->config.hw_backed == kHardenedBoolTrue) {
    HARDENED_CHECK_EQ(launder32(private_key->config.hw_backed),
                      kHardenedBoolTrue);
    HARDENED_TRY_WIPE_DMEM(keyblob_sideload_key_otbn(private_key));
    HARDENED_TRY_WIPE_DMEM(p384_sideload_ecdh_start(pk));
  } else if (private_key->config.hw_backed == kHardenedBoolFalse) {
    HARDENED_CHECK_EQ(launder32(private_key->config.hw_backed),
                      kHardenedBoolFalse);
    p384_masked_scalar_t private_scalar;
    HARDENED_TRY(hardened_memcpy(private_scalar.share0, private_key->keyblob,
                                 kP384MaskedScalarTotalShareWords));
    HARDENED_CHECK_EQ(
        hardened_memeq(private_key->keyblob, private_scalar.share0,
                       kP384MaskedScalarTotalShareWords),
        kHardenedBoolTrue);
    private_scalar.checksum = p384_masked_scalar_checksum(&private_scalar);
    HARDENED_TRY_WIPE_DMEM(p384_ecdh_start(&private_scalar, pk));
  } else {
    // Invalid value for `hw_backed`.
    // COVERAGE (MISSING) We do not cover bad hw_backed inputs.
    return OTCRYPTO_BAD_ARGS;
  }

  // To detect forgeries of the pointers to the public and private key that we
  // have passed to the ECC implementation, check again their integrity. If the
  // pointers would have been tampered with between the first integrity check we
  // did when entering the CryptoLib and here, we would detect this now.
  HARDENED_CHECK_EQ(integrity_blinded_key_check(private_key),
                    kHardenedBoolTrue);
  HARDENED_CHECK_EQ(integrity_unblinded_key_check(public_key),
                    kHardenedBoolTrue);

  return otcrypto_eval_exit(OTCRYPTO_OK);
}

otcrypto_status_t otcrypto_ecdh_p384_async_finalize(
    otcrypto_blinded_key_t *shared_secret) {
  if (shared_secret == NULL || shared_secret->keyblob == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Randomize the output before computing it.
  HARDENED_TRY(hardened_memshred(shared_secret->keyblob, kP384CoordWords));

  // Shared keys cannot be sideloaded because they are software-generated.
  if (shared_secret->config.hw_backed != kHardenedBoolFalse) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(launder32(shared_secret->config.hw_backed),
                    kHardenedBoolFalse);

  // Check shared secret length.
  if (shared_secret->config.key_length != kP384CoordBytes) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(launder32(shared_secret->config.key_length),
                    kP384CoordBytes);
  if (shared_secret->keyblob_length !=
      keyblob_num_words(shared_secret->config) * sizeof(uint32_t)) {
    // COVERAGE (MISSING) We do not cover bad keyblob length inputs.
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(
      shared_secret->keyblob_length,
      keyblob_num_words(shared_secret->config) * sizeof(uint32_t));

  // Note: This operation wipes DMEM after retrieving the keys, so if an error
  // occurs after this point then the keys would be unrecoverable. This should
  // be the last potentially error-causing line before returning to the caller.
  p384_ecdh_shared_key_t ss;
  HARDENED_TRY(hardened_memshred(ss.share0, ARRAYSIZE(ss.share0)));
  HARDENED_TRY(hardened_memshred(ss.share1, ARRAYSIZE(ss.share1)));
  HARDENED_TRY_WIPE_DMEM(p384_ecdh_finalize(&ss));
  HARDENED_CHECK_EQ(p384_ecdh_shared_key_checksum_check(&ss),
                    kHardenedBoolTrue);
  HARDENED_TRY(keyblob_from_shares(ss.share0, ss.share1, shared_secret->config,
                                   shared_secret->keyblob));

  // Set the checksum.
  shared_secret->checksum = integrity_blinded_checksum(shared_secret);

  // Clear the OTBN sideload slot (in case the seed was sideloaded).
  return otcrypto_eval_exit(keymgr_sideload_clear_otbn());
}

otcrypto_status_t otcrypto_ecc_p384_public_key_import(
    const otcrypto_const_word32_buf_t x, const otcrypto_const_word32_buf_t y,
    otcrypto_unblinded_key_t *public_key) {
  if (x.data == NULL || y.data == NULL || public_key == NULL ||
      public_key->key == NULL) {
    // COVERAGE (MISSING) We do not cover null inputs.
    return OTCRYPTO_BAD_ARGS;
  }

  // Check the lengths of the input coordinate buffers.
  if (x.len != kP384CoordWords || y.len != kP384CoordWords) {
    // COVERAGE (MISSING) We do not cover bad length inputs.
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(launder32(x.len), kP384CoordWords);
  HARDENED_CHECK_EQ(launder32(y.len), kP384CoordWords);

  // Check the output key mode; both ECDSA and ECDH P-384 public key modes are
  // accepted since the underlying point representation is the same.
  if (public_key->key_mode != kOtcryptoKeyModeEcdsaP384 &&
      public_key->key_mode != kOtcryptoKeyModeEcdhP384) {
    // COVERAGE (MISSING) We do not cover bad key_mode inputs.
    return OTCRYPTO_BAD_ARGS;
  }

  // Check the output key length (must fit a p384_point_t).
  HARDENED_TRY(p384_public_key_length_check(public_key));

  // Copy the coordinates into the output key buffer.
  p384_point_t *pt = (p384_point_t *)public_key->key;
  HARDENED_TRY(hardened_memcpy(pt->x, x.data, kP384CoordWords));
  HARDENED_TRY(hardened_memcpy(pt->y, y.data, kP384CoordWords));

  // Calculate the public key checksum.
  public_key->checksum = integrity_unblinded_checksum(public_key);

  return otcrypto_eval_exit(OTCRYPTO_OK);
}

otcrypto_status_t otcrypto_ecc_p384_public_key_export(
    const otcrypto_unblinded_key_t *public_key, otcrypto_word32_buf_t *x,
    otcrypto_word32_buf_t *y) {
  if (x == NULL || x->data == NULL || y == NULL || y->data == NULL ||
      public_key == NULL || public_key->key == NULL) {
    // COVERAGE (MISSING) We do not cover null inputs.
    return OTCRYPTO_BAD_ARGS;
  }

  // Check the lengths of the output coordinate buffers.
  if (x->len != kP384CoordWords || y->len != kP384CoordWords) {
    // COVERAGE (MISSING) We do not cover bad length inputs.
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(launder32(x->len), kP384CoordWords);
  HARDENED_CHECK_EQ(launder32(y->len), kP384CoordWords);

  // Check the output key mode; both ECDSA and ECDH P-384 public key modes are
  // accepted since the underlying point representation is the same.
  if (public_key->key_mode != kOtcryptoKeyModeEcdsaP384 &&
      public_key->key_mode != kOtcryptoKeyModeEcdhP384) {
    // COVERAGE (MISSING) We do not cover bad key_mode inputs.
    return OTCRYPTO_BAD_ARGS;
  }

  // Check the key length.
  HARDENED_TRY(p384_public_key_length_check(public_key));

  // Check the integrity of the public key.
  if (integrity_unblinded_key_check(public_key) != kHardenedBoolTrue) {
    // COVERAGE (MISSING) We do not cover bad integrity set keys.
    return OTCRYPTO_BAD_ARGS;
  }

  // Copy the key into the output buffer.
  p384_point_t *pt = (p384_point_t *)public_key->key;
  HARDENED_TRY(hardened_memcpy(x->data, pt->x, kP384CoordWords));
  HARDENED_TRY(hardened_memcpy(y->data, pt->y, kP384CoordWords));

  return otcrypto_eval_exit(OTCRYPTO_OK);
}

otcrypto_status_t otcrypto_ecc_p384_private_key_import(
    otcrypto_const_word32_buf_t share0, otcrypto_const_word32_buf_t share1,
    otcrypto_blinded_key_t *private_key) {
  if (share0.data == NULL || share1.data == NULL || private_key == NULL ||
      private_key->keyblob == NULL) {
    // COVERAGE (MISSING) We do not cover null inputs.
    return OTCRYPTO_BAD_ARGS;
  }

  // Each share must be 448 bits (384-bit scalar + 64 redundant bits for
  // side-channel protection).
  if (share0.len != kP384MaskedScalarShareWords ||
      share1.len != kP384MaskedScalarShareWords) {
    // COVERAGE (MISSING) We do not cover bad length inputs.
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(launder32(share0.len), kP384MaskedScalarShareWords);
  HARDENED_CHECK_EQ(launder32(share1.len), kP384MaskedScalarShareWords);

  // Check the key mode; both ECDSA and ECDH P-384 modes are accepted since
  // the private key representation is identical for both.
  if (private_key->config.key_mode != kOtcryptoKeyModeEcdsaP384 &&
      private_key->config.key_mode != kOtcryptoKeyModeEcdhP384) {
    // COVERAGE (MISSING) We do not cover bad key_mode inputs.
    return OTCRYPTO_BAD_ARGS;
  }

  // Import is only supported for software-backed keys.
  if (private_key->config.hw_backed != kHardenedBoolFalse) {
    // COVERAGE (MISSING) We do not cover bad hw_backed inputs.
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(launder32(private_key->config.hw_backed),
                    kHardenedBoolFalse);

  // Check that the caller-allocated keyblob matches the expected P-384 layout.
  HARDENED_TRY(p384_private_key_length_check(private_key));

  // Randomize the keyblob before writing secret data.
  HARDENED_TRY(hardened_memshred(private_key->keyblob,
                                 kP384MaskedScalarTotalShareWords));

  // Copy the caller-supplied shares into the keyblob as share0 || share1,
  // matching the p384_masked_scalar_t layout.
  HARDENED_TRY(hardened_memcpy(private_key->keyblob, share0.data,
                               kP384MaskedScalarShareWords));
  HARDENED_TRY(
      hardened_memcpy(private_key->keyblob + kP384MaskedScalarShareWords,
                      share1.data, kP384MaskedScalarShareWords));

  // Set the blinded key checksum.
  private_key->checksum = integrity_blinded_checksum(private_key);

  return otcrypto_eval_exit(OTCRYPTO_OK);
}

otcrypto_status_t otcrypto_ecc_p384_private_key_export(
    const otcrypto_blinded_key_t *private_key, otcrypto_word32_buf_t *share0,
    otcrypto_word32_buf_t *share1) {
  if (share0 == NULL || share0->data == NULL || share1 == NULL ||
      share1->data == NULL || private_key == NULL ||
      private_key->keyblob == NULL) {
    // COVERAGE (MISSING) We do not cover null inputs.
    return OTCRYPTO_BAD_ARGS;
  }

  // Check the output buffer lengths: each must be exactly 448 bits (384-bit
  // scalar + 64 redundant bits for side-channel protection).
  if (share0->len != kP384MaskedScalarShareWords ||
      share1->len != kP384MaskedScalarShareWords) {
    // COVERAGE (MISSING) We do not cover bad length inputs.
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(launder32(share0->len), kP384MaskedScalarShareWords);
  HARDENED_CHECK_EQ(launder32(share1->len), kP384MaskedScalarShareWords);

  // Check the key mode; both ECDSA and ECDH P-384 modes are accepted since
  // the private key representation is identical for both.
  if (private_key->config.key_mode != kOtcryptoKeyModeEcdsaP384 &&
      private_key->config.key_mode != kOtcryptoKeyModeEcdhP384) {
    // COVERAGE (MISSING) We do not cover bad key_mode inputs.
    return OTCRYPTO_BAD_ARGS;
  }

  // Export is only supported for software-backed keys.
  if (private_key->config.hw_backed != kHardenedBoolFalse) {
    // COVERAGE (MISSING) We do not cover bad hw_backed inputs.
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(launder32(private_key->config.hw_backed),
                    kHardenedBoolFalse);

  // Check that the key is marked exportable.
  if (launder32(private_key->config.exportable) != kHardenedBoolTrue) {
    // COVERAGE (MISSING) We do not cover non exportable inputs.
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(private_key->config.exportable, kHardenedBoolTrue);

  // Check that the private key length is correct.
  HARDENED_TRY(p384_private_key_length_check(private_key));

  // Check the integrity of the provided private key.
  if (integrity_blinded_key_check(private_key) != kHardenedBoolTrue) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Randomize output buffers before writing secret data.
  HARDENED_TRY(hardened_memshred(share0->data, kP384MaskedScalarShareWords));
  HARDENED_TRY(hardened_memshred(share1->data, kP384MaskedScalarShareWords));

  // Copy the keyblob shares into the caller-supplied output buffers.
  HARDENED_TRY(hardened_memcpy(share0->data, private_key->keyblob,
                               kP384MaskedScalarShareWords));
  HARDENED_TRY(hardened_memcpy(
      share1->data, private_key->keyblob + kP384MaskedScalarShareWords,
      kP384MaskedScalarShareWords));

  return otcrypto_eval_exit(OTCRYPTO_OK);
}

otcrypto_status_t otcrypto_ecc_p384_arith_share_private_key(
    const otcrypto_const_word32_buf_t *bool_private_key_share0,
    const otcrypto_const_word32_buf_t *bool_private_key_share1,
    otcrypto_blinded_key_t *arith_private_key) {
  if (bool_private_key_share0 == NULL || bool_private_key_share1 == NULL ||
      arith_private_key == NULL || arith_private_key->keyblob == NULL) {
    // COVERAGE (MISSING) We do not cover null inputs.
    return OTCRYPTO_BAD_ARGS;
  }

  // The key shares must resided in 448-bit buffers.
  if (bool_private_key_share0->len != kP384MaskedScalarShareWords ||
      bool_private_key_share1->len != kP384MaskedScalarShareWords) {
    // COVERAGE (MISSING) We do not cover bad length inputs.
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(launder32(bool_private_key_share0->len),
                    kP384MaskedScalarShareWords);
  HARDENED_CHECK_EQ(launder32(bool_private_key_share1->len),
                    kP384MaskedScalarShareWords);

  // Check the key mode; both ECDSA and ECDH P-384 modes are accepted since
  // the private key representation is identical for both.
  if (arith_private_key->config.key_mode != kOtcryptoKeyModeEcdsaP384 &&
      arith_private_key->config.key_mode != kOtcryptoKeyModeEcdhP384) {
    // COVERAGE (MISSING) We do not cover bad key_mode inputs.
    return OTCRYPTO_BAD_ARGS;
  }

  // Import is only supported for software-backed keys.
  if (arith_private_key->config.hw_backed != kHardenedBoolFalse) {
    // COVERAGE (MISSING) We do not cover bad hw_backed inputs.
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(launder32(arith_private_key->config.hw_backed),
                    kHardenedBoolFalse);

  // Check that the caller-allocated keyblob matches the expected P-384 layout.
  HARDENED_TRY(p384_private_key_length_check(arith_private_key));

  // Randomize the keyblob before writing secret data.
  HARDENED_TRY(hardened_memshred(arith_private_key->keyblob,
                                 kP384MaskedScalarTotalShareWords));

  p384_masked_scalar_t boolean_private_scalar;
  p384_masked_scalar_t arith_private_scalar;
  HARDENED_TRY(hardened_memcpy(boolean_private_scalar.share0,
                               bool_private_key_share0->data,
                               kP384MaskedScalarShareWords));
  HARDENED_TRY(hardened_memcpy(boolean_private_scalar.share1,
                               bool_private_key_share1->data,
                               kP384MaskedScalarShareWords));
  boolean_private_scalar.checksum =
      p384_masked_scalar_checksum(&boolean_private_scalar);

  // Invoke the sharing routine.
  HARDENED_TRY_WIPE_DMEM(p384_arith_share_private_key(&boolean_private_scalar,
                                                      &arith_private_scalar));

  // Copy the two arithmetic shares into the output buffer.
  HARDENED_TRY(hardened_memcpy(arith_private_key->keyblob,
                               arith_private_scalar.share0,
                               kP384MaskedScalarTotalShareWords));

  // Set the shared key checksum.
  arith_private_key->checksum = integrity_blinded_checksum(arith_private_key);

  HARDENED_CHECK_EQ(OTCRYPTO_CHECK_BUF(bool_private_key_share0),
                    kHardenedBoolTrue);
  HARDENED_CHECK_EQ(OTCRYPTO_CHECK_BUF(bool_private_key_share1),
                    kHardenedBoolTrue);

  return otcrypto_eval_exit(OTCRYPTO_OK);
}
