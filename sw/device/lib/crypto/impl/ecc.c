// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/include/ecc.h"

#include "sw/device/lib/crypto/drivers/entropy.h"
#include "sw/device/lib/crypto/drivers/hmac.h"
#include "sw/device/lib/crypto/impl/ecc/p256.h"
#include "sw/device/lib/crypto/impl/ecc/p384.h"
#include "sw/device/lib/crypto/impl/integrity.h"
#include "sw/device/lib/crypto/impl/keyblob.h"
#include "sw/device/lib/crypto/include/datatypes.h"

// Module ID for status codes.
#define MODULE_ID MAKE_MODULE_ID('e', 'c', 'c')

otcrypto_status_t otcrypto_ecdsa_keygen(
    const otcrypto_ecc_curve_t *elliptic_curve,
    otcrypto_blinded_key_t *private_key, otcrypto_unblinded_key_t *public_key) {
  HARDENED_TRY(otcrypto_ecdsa_keygen_async_start(elliptic_curve, private_key));
  return otcrypto_ecdsa_keygen_async_finalize(elliptic_curve, private_key,
                                              public_key);
}

otcrypto_status_t otcrypto_ecdsa_sign(
    const otcrypto_blinded_key_t *private_key,
    const otcrypto_hash_digest_t message_digest,
    const otcrypto_ecc_curve_t *elliptic_curve,
    otcrypto_word32_buf_t signature) {
  HARDENED_TRY(otcrypto_ecdsa_sign_async_start(private_key, message_digest,
                                               elliptic_curve));
  return otcrypto_ecdsa_sign_async_finalize(elliptic_curve, signature);
}

otcrypto_status_t otcrypto_ecdsa_verify(
    const otcrypto_unblinded_key_t *public_key,
    const otcrypto_hash_digest_t message_digest,
    otcrypto_const_word32_buf_t signature,
    const otcrypto_ecc_curve_t *elliptic_curve,
    hardened_bool_t *verification_result) {
  HARDENED_TRY(otcrypto_ecdsa_verify_async_start(public_key, message_digest,
                                                 signature, elliptic_curve));
  return otcrypto_ecdsa_verify_async_finalize(elliptic_curve, signature,
                                              verification_result);
}

otcrypto_status_t otcrypto_ecdh_keygen(
    const otcrypto_ecc_curve_t *elliptic_curve,
    otcrypto_blinded_key_t *private_key, otcrypto_unblinded_key_t *public_key) {
  HARDENED_TRY(otcrypto_ecdh_keygen_async_start(elliptic_curve, private_key));
  return otcrypto_ecdh_keygen_async_finalize(elliptic_curve, private_key,
                                             public_key);
}

otcrypto_status_t otcrypto_ecdh(const otcrypto_blinded_key_t *private_key,
                                const otcrypto_unblinded_key_t *public_key,
                                const otcrypto_ecc_curve_t *elliptic_curve,
                                otcrypto_blinded_key_t *shared_secret) {
  HARDENED_TRY(
      otcrypto_ecdh_async_start(private_key, public_key, elliptic_curve));
  return otcrypto_ecdh_async_finalize(elliptic_curve, shared_secret);
}

otcrypto_status_t otcrypto_ed25519_keygen(
    otcrypto_blinded_key_t *private_key, otcrypto_unblinded_key_t *public_key) {
  // TODO: Ed25519 is not yet implemented.
  return OTCRYPTO_NOT_IMPLEMENTED;
}

otcrypto_status_t otcrypto_ed25519_sign(
    const otcrypto_blinded_key_t *private_key,
    otcrypto_const_byte_buf_t input_message,
    otcrypto_eddsa_sign_mode_t sign_mode, otcrypto_word32_buf_t signature) {
  // TODO: Ed25519 is not yet implemented.
  return OTCRYPTO_NOT_IMPLEMENTED;
}

otcrypto_status_t otcrypto_ed25519_verify(
    const otcrypto_unblinded_key_t *public_key,
    otcrypto_const_byte_buf_t input_message,
    otcrypto_eddsa_sign_mode_t sign_mode, otcrypto_const_word32_buf_t signature,
    hardened_bool_t *verification_result) {
  // TODO: Ed25519 is not yet implemented.
  return OTCRYPTO_NOT_IMPLEMENTED;
}

otcrypto_status_t otcrypto_x25519_keygen(otcrypto_blinded_key_t *private_key,
                                         otcrypto_unblinded_key_t *public_key) {
  // TODO: Connect X25519 operations to API.
  return OTCRYPTO_NOT_IMPLEMENTED;
}

otcrypto_status_t otcrypto_x25519(const otcrypto_blinded_key_t *private_key,
                                  const otcrypto_unblinded_key_t *public_key,
                                  otcrypto_blinded_key_t *shared_secret) {
  // TODO: Connect X25519 operations to API.
  return OTCRYPTO_NOT_IMPLEMENTED;
}

/**
 * Calls keymgr to sideload key material into OTBN.
 *
 * This routine should only ever be called on hardware-backed keys.
 *
 * @param private_key Sideloaded key handle.
 * @return OK or error.
 */
OT_WARN_UNUSED_RESULT
static status_t sideload_key_seed(const otcrypto_blinded_key_t *private_key) {
  keymgr_diversification_t diversification;
  HARDENED_TRY(
      keyblob_to_keymgr_diversification(private_key, &diversification));
  return keymgr_generate_key_otbn(diversification);
}

otcrypto_status_t otcrypto_ecdsa_keygen_async_start(
    const otcrypto_ecc_curve_t *elliptic_curve,
    const otcrypto_blinded_key_t *private_key) {
  if (elliptic_curve == NULL || private_key == NULL ||
      private_key->keyblob == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Check the key mode.
  if (launder32(private_key->config.key_mode) != kOtcryptoKeyModeEcdsa) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(private_key->config.key_mode, kOtcryptoKeyModeEcdsa);

  // Check that the entropy complex is initialized.
  HARDENED_TRY(entropy_complex_check());

  // Select the correct keygen operation and start it.
  switch (launder32(elliptic_curve->curve_type)) {
    case kOtcryptoEccCurveTypeNistP256:
      HARDENED_CHECK_EQ(elliptic_curve->curve_type,
                        kOtcryptoEccCurveTypeNistP256);
      if (launder32(private_key->config.hw_backed) == kHardenedBoolTrue) {
        HARDENED_CHECK_EQ(private_key->config.hw_backed, kHardenedBoolTrue);
        HARDENED_TRY(sideload_key_seed(private_key));
        return p256_sideload_keygen_start();
      } else if (launder32(private_key->config.hw_backed) ==
                 kHardenedBoolFalse) {
        HARDENED_CHECK_EQ(private_key->config.hw_backed, kHardenedBoolFalse);
        return p256_keygen_start();
      } else {
        return OTCRYPTO_BAD_ARGS;
      }
      return OTCRYPTO_OK;
    case kOtcryptoEccCurveTypeNistP384:
      HARDENED_CHECK_EQ(elliptic_curve->curve_type,
                        kOtcryptoEccCurveTypeNistP384);
      if (launder32(private_key->config.hw_backed) == kHardenedBoolTrue) {
        HARDENED_CHECK_EQ(private_key->config.hw_backed, kHardenedBoolTrue);
        HARDENED_TRY(sideload_key_seed(private_key));
        return p384_sideload_keygen_start();
      } else if (launder32(private_key->config.hw_backed) ==
                 kHardenedBoolFalse) {
        HARDENED_CHECK_EQ(private_key->config.hw_backed, kHardenedBoolFalse);
        return p384_keygen_start();
      } else {
        return OTCRYPTO_BAD_ARGS;
      }
      return OTCRYPTO_OK;
    case kEccCurveTypeBrainpoolP256R1:
      OT_FALLTHROUGH_INTENDED;
    case kOtcryptoEccCurveTypeCustom:
      // TODO: Implement support for other curves.
      return OTCRYPTO_NOT_IMPLEMENTED;
    default:
      return OTCRYPTO_BAD_ARGS;
  }

  // Should never get here.
  HARDENED_TRAP();
  return OTCRYPTO_FATAL_ERR;
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

  if (launder32(private_key->config.hw_backed) == kHardenedBoolTrue) {
    // Skip the length check in this case; if the salt is the wrong length, the
    // keyblob library will catch it before we sideload the key.
    return OTCRYPTO_OK;
  }
  HARDENED_CHECK_NE(private_key->config.hw_backed, kHardenedBoolTrue);

  // Check the unmasked length.
  if (launder32(private_key->config.key_length) != kP384ScalarBytes) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(private_key->config.key_length, kP384ScalarBytes);

  // Check the single-share length.
  if (launder32(keyblob_share_num_words(private_key->config)) !=
      kP384MaskedScalarShareWords) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(keyblob_share_num_words(private_key->config),
                    kP384MaskedScalarShareWords);

  // Check the keyblob length.
  if (launder32(private_key->keyblob_length) != sizeof(p384_masked_scalar_t)) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(private_key->keyblob_length, sizeof(p384_masked_scalar_t));

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
  if (launder32(public_key->key_length) != sizeof(p384_point_t)) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(public_key->key_length, sizeof(p384_point_t));
  return OTCRYPTO_OK;
}

/**
 * Finalize a keypair generation operation for curve P-256.
 *
 * This function assumes that space is already allocated for all key material
 * and that the length parameters on the structs are set accordingly, in the
 * same way as for `otcrypto_ecdh_keygen_async_finalize` and
 * `otcrypto_ecdsa_keygen_async_finalize`.
 *
 * @param[out] private_key Private key to populate.
 * @param[out] public_key Public key to populate.
 * @return OK or error.
 */
OT_WARN_UNUSED_RESULT
static status_t internal_p256_keygen_finalize(
    otcrypto_blinded_key_t *private_key, otcrypto_unblinded_key_t *public_key) {
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
    p256_masked_scalar_t *sk = (p256_masked_scalar_t *)private_key->keyblob;
    HARDENED_TRY(p256_keygen_finalize(sk, pk));
    private_key->checksum = integrity_blinded_checksum(private_key);
  } else {
    return OTCRYPTO_BAD_ARGS;
  }

  // Prepare the public key.
  public_key->checksum = integrity_unblinded_checksum(public_key);

  // Clear the OTBN sideload slot (in case the seed was sideloaded).
  return keymgr_sideload_clear_otbn();
}

/**
 * Finalize a keypair generation operation for curve P-384.
 *
 * This function assumes that space is already allocated for all key material
 * and that the length parameters on the structs are set accordingly, in the
 * same way as for `otcrypto_ecdh_keygen_async_finalize` and
 * `otcrypto_ecdsa_keygen_async_finalize`.
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

  if (launder32(private_key->config.hw_backed) == kHardenedBoolTrue) {
    // Note: This operation wipes DMEM after retrieving the keys, so if an error
    // occurs after this point then the keys would be unrecoverable. This should
    // be the last potentially error-causing line before returning to the
    // caller.
    HARDENED_CHECK_EQ(private_key->config.hw_backed, kHardenedBoolTrue);
    HARDENED_TRY(p384_sideload_keygen_finalize(pk));
  } else if (launder32(private_key->config.hw_backed) == kHardenedBoolFalse) {
    p384_masked_scalar_t *sk = (p384_masked_scalar_t *)private_key->keyblob;
    // Note: This operation wipes DMEM after retrieving the keys, so if an error
    // occurs after this point then the keys would be unrecoverable. This should
    // be the last potentially error-causing line before returning to the
    // caller.
    HARDENED_CHECK_EQ(private_key->config.hw_backed, kHardenedBoolFalse);
    HARDENED_TRY(p384_keygen_finalize(sk, pk));
    private_key->checksum = integrity_blinded_checksum(private_key);
  } else {
    return OTCRYPTO_BAD_ARGS;
  }

  public_key->checksum = integrity_unblinded_checksum(public_key);
  return OTCRYPTO_OK;
}

otcrypto_status_t otcrypto_ecdsa_keygen_async_finalize(
    const otcrypto_ecc_curve_t *elliptic_curve,
    otcrypto_blinded_key_t *private_key, otcrypto_unblinded_key_t *public_key) {
  // Check for any NULL pointers.
  if (elliptic_curve == NULL || private_key == NULL || public_key == NULL ||
      private_key->keyblob == NULL || public_key->key == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Check the key modes.
  if (launder32(private_key->config.key_mode) != kOtcryptoKeyModeEcdsa ||
      launder32(public_key->key_mode) != kOtcryptoKeyModeEcdsa) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(private_key->config.key_mode, kOtcryptoKeyModeEcdsa);
  HARDENED_CHECK_EQ(public_key->key_mode, kOtcryptoKeyModeEcdsa);

  // Select the correct keygen operation and finalize it.
  switch (launder32(elliptic_curve->curve_type)) {
    case kOtcryptoEccCurveTypeNistP256:
      HARDENED_CHECK_EQ(elliptic_curve->curve_type,
                        kOtcryptoEccCurveTypeNistP256);
      HARDENED_TRY(internal_p256_keygen_finalize(private_key, public_key));
      break;
    case kOtcryptoEccCurveTypeNistP384:
      HARDENED_CHECK_EQ(elliptic_curve->curve_type,
                        kOtcryptoEccCurveTypeNistP384);
      HARDENED_TRY(internal_p384_keygen_finalize(private_key, public_key));
      break;
    case kEccCurveTypeBrainpoolP256R1:
      OT_FALLTHROUGH_INTENDED;
    case kOtcryptoEccCurveTypeCustom:
      // TODO: Implement support for other curves.
      return OTCRYPTO_NOT_IMPLEMENTED;
    default:
      return OTCRYPTO_BAD_ARGS;
  }

  // Clear the OTBN sideload slot (in case the seed was sideloaded).
  return keymgr_sideload_clear_otbn();
}

/**
 * Start an ECDSA signature generation operation for curve P-256.
 *
 * @param private_key Private key to sign with.
 * @param message_digest Message digest to sign.
 * @return OK or error.
 */
OT_WARN_UNUSED_RESULT
static status_t internal_ecdsa_p256_sign_start(
    const otcrypto_blinded_key_t *private_key,
    const otcrypto_hash_digest_t message_digest) {
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
    HARDENED_TRY(sideload_key_seed(private_key));
    return p256_ecdsa_sideload_sign_start(message_digest.data);
  }

  // Invalid value for private_key->hw_backed.
  return OTCRYPTO_BAD_ARGS;
}

/**
 * Start an ECDSA signature generation operation for curve P-384.
 *
 * @param private_key Private key to sign with.
 * @param message_digest Message digest to sign.
 * @return OK or error.
 */
OT_WARN_UNUSED_RESULT
static status_t internal_ecdsa_p384_sign_start(
    const otcrypto_blinded_key_t *private_key,
    const otcrypto_hash_digest_t message_digest) {
  // Check the digest length.
  if (launder32(message_digest.len) != kP384ScalarWords) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(message_digest.len, kP384ScalarWords);

  // Check the key length.
  HARDENED_TRY(p384_private_key_length_check(private_key));

  if (launder32(private_key->config.hw_backed) == kHardenedBoolFalse) {
    // Start the asynchronous signature-generation routine.
    HARDENED_CHECK_EQ(private_key->config.hw_backed, kHardenedBoolFalse);
    p384_masked_scalar_t *sk = (p384_masked_scalar_t *)private_key->keyblob;
    return p384_ecdsa_sign_start(message_digest.data, sk);
  } else if (launder32(private_key->config.hw_backed) == kHardenedBoolTrue) {
    // Load the key and start in sideloaded-key mode.
    HARDENED_CHECK_EQ(private_key->config.hw_backed, kHardenedBoolTrue);
    HARDENED_TRY(sideload_key_seed(private_key));
    return p384_ecdsa_sideload_sign_start(message_digest.data);
  }

  // Invalid value for private_key->hw_backed.
  return OTCRYPTO_BAD_ARGS;
}

otcrypto_status_t otcrypto_ecdsa_sign_async_start(
    const otcrypto_blinded_key_t *private_key,
    const otcrypto_hash_digest_t message_digest,
    const otcrypto_ecc_curve_t *elliptic_curve) {
  if (private_key == NULL || private_key->keyblob == NULL ||
      elliptic_curve == NULL || message_digest.data == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Check the integrity of the private key.
  if (launder32(integrity_blinded_key_check(private_key)) !=
      kHardenedBoolTrue) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(integrity_blinded_key_check(private_key),
                    kHardenedBoolTrue);

  // Check the private key mode.
  if (launder32(private_key->config.key_mode) != kOtcryptoKeyModeEcdsa) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(private_key->config.key_mode, kOtcryptoKeyModeEcdsa);

  // Check that the entropy complex is initialized.
  HARDENED_TRY(entropy_complex_check());

  // Select the correct signing operation and start it.
  switch (launder32(elliptic_curve->curve_type)) {
    case kOtcryptoEccCurveTypeNistP256:
      HARDENED_CHECK_EQ(elliptic_curve->curve_type,
                        kOtcryptoEccCurveTypeNistP256);
      HARDENED_TRY(internal_ecdsa_p256_sign_start(private_key, message_digest));
      return OTCRYPTO_OK;
    case kOtcryptoEccCurveTypeNistP384:
      HARDENED_CHECK_EQ(elliptic_curve->curve_type,
                        kOtcryptoEccCurveTypeNistP384);
      HARDENED_TRY(internal_ecdsa_p384_sign_start(private_key, message_digest));
      return OTCRYPTO_OK;
    case kEccCurveTypeBrainpoolP256R1:
      OT_FALLTHROUGH_INTENDED;
    case kOtcryptoEccCurveTypeCustom:
      // TODO: Implement support for other curves.
      return OTCRYPTO_NOT_IMPLEMENTED;
    default:
      return OTCRYPTO_BAD_ARGS;
  }

  // Should never get here.
  HARDENED_TRAP();
  return OTCRYPTO_FATAL_ERR;
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
  if (launder32(len) > UINT32_MAX / sizeof(uint32_t) ||
      launder32(len) * sizeof(uint32_t) != sizeof(p384_ecdsa_signature_t)) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(len * sizeof(uint32_t), sizeof(p384_ecdsa_signature_t));

  return OTCRYPTO_OK;
}

otcrypto_status_t otcrypto_ecdsa_sign_async_finalize(
    const otcrypto_ecc_curve_t *elliptic_curve,
    otcrypto_word32_buf_t signature) {
  if (elliptic_curve == NULL || signature.data == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Select the correct signing operation and finalize it.
  switch (launder32(elliptic_curve->curve_type)) {
    case kOtcryptoEccCurveTypeNistP256:
      HARDENED_CHECK_EQ(elliptic_curve->curve_type,
                        kOtcryptoEccCurveTypeNistP256);
      HARDENED_TRY(p256_signature_length_check(signature.len));
      p256_ecdsa_signature_t *sig_p256 =
          (p256_ecdsa_signature_t *)signature.data;
      // Note: This operation wipes DMEM, so if an error occurs after this
      // point then the signature would be unrecoverable. This should be the
      // last potentially error-causing line before returning to the caller.
      HARDENED_TRY(p256_ecdsa_sign_finalize(sig_p256));
      break;
    case kOtcryptoEccCurveTypeNistP384:
      HARDENED_CHECK_EQ(elliptic_curve->curve_type,
                        kOtcryptoEccCurveTypeNistP384);
      HARDENED_TRY(p384_signature_length_check(signature.len));
      p384_ecdsa_signature_t *sig_p384 =
          (p384_ecdsa_signature_t *)signature.data;
      // Note: This operation wipes DMEM, so if an error occurs after this
      // point then the signature would be unrecoverable. This should be the
      // last potentially error-causing line before returning to the caller.
      HARDENED_TRY(p384_ecdsa_sign_finalize(sig_p384));
      break;
    case kEccCurveTypeBrainpoolP256R1:
      OT_FALLTHROUGH_INTENDED;
    case kOtcryptoEccCurveTypeCustom:
      // TODO: Implement support for other curves.
      return OTCRYPTO_NOT_IMPLEMENTED;
    default:
      return OTCRYPTO_BAD_ARGS;
  }

  // Clear the OTBN sideload slot (in case the key was sideloaded).
  return keymgr_sideload_clear_otbn();
}

/**
 * Start an ECDSA signature verification operation for curve P-256.
 *
 * @param public_key Public key to check against.
 * @param message_digest Message digest to check against.
 * @param signature Signature to verify.
 * @return OK or error.
 */
OT_WARN_UNUSED_RESULT
static status_t internal_ecdsa_p256_verify_start(
    const otcrypto_unblinded_key_t *public_key,
    const otcrypto_hash_digest_t message_digest,
    otcrypto_const_word32_buf_t signature) {
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

/**
 * Start an ECDSA signature verification operation for curve P-384.
 *
 * @param public_key Public key to check against.
 * @param message_digest Message digest to check against.
 * @param signature Signature to verify.
 * @return OK or error.
 */
OT_WARN_UNUSED_RESULT
static status_t internal_ecdsa_p384_verify_start(
    const otcrypto_unblinded_key_t *public_key,
    const otcrypto_hash_digest_t message_digest,
    otcrypto_const_word32_buf_t signature) {
  // Check the public key size.
  HARDENED_TRY(p384_public_key_length_check(public_key));
  p384_point_t *pk = (p384_point_t *)public_key->key;

  // Check the digest length.
  if (launder32(message_digest.len) != kP384ScalarWords) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(message_digest.len, kP384ScalarWords);

  // Check the signature lengths.
  HARDENED_TRY(p384_signature_length_check(signature.len));
  p384_ecdsa_signature_t *sig = (p384_ecdsa_signature_t *)signature.data;

  // Start the asynchronous signature-verification routine.
  return p384_ecdsa_verify_start(sig, message_digest.data, pk);
}

otcrypto_status_t otcrypto_ecdsa_verify_async_start(
    const otcrypto_unblinded_key_t *public_key,
    const otcrypto_hash_digest_t message_digest,
    otcrypto_const_word32_buf_t signature,
    const otcrypto_ecc_curve_t *elliptic_curve) {
  if (public_key == NULL || elliptic_curve == NULL || signature.data == NULL ||
      message_digest.data == NULL || public_key->key == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Check the public key mode.
  if (launder32(public_key->key_mode) != kOtcryptoKeyModeEcdsa) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(public_key->key_mode, kOtcryptoKeyModeEcdsa);

  // Check the integrity of the public key.
  if (launder32(integrity_unblinded_key_check(public_key)) !=
      kHardenedBoolTrue) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(integrity_unblinded_key_check(public_key),
                    kHardenedBoolTrue);

  // Select the correct verification operation and start it.
  switch (launder32(elliptic_curve->curve_type)) {
    case kOtcryptoEccCurveTypeNistP256:
      HARDENED_CHECK_EQ(elliptic_curve->curve_type,
                        kOtcryptoEccCurveTypeNistP256);
      HARDENED_TRY(internal_ecdsa_p256_verify_start(public_key, message_digest,
                                                    signature));
      return OTCRYPTO_OK;
    case kOtcryptoEccCurveTypeNistP384:
      HARDENED_CHECK_EQ(elliptic_curve->curve_type,
                        kOtcryptoEccCurveTypeNistP384);
      HARDENED_TRY(internal_ecdsa_p384_verify_start(public_key, message_digest,
                                                    signature));
      return OTCRYPTO_OK;
    case kEccCurveTypeBrainpoolP256R1:
      OT_FALLTHROUGH_INTENDED;
    case kOtcryptoEccCurveTypeCustom:
      // TODO: Implement support for other curves.
      return OTCRYPTO_NOT_IMPLEMENTED;
    default:
      return OTCRYPTO_BAD_ARGS;
  }

  // Should never get here.
  HARDENED_TRAP();
  return OTCRYPTO_FATAL_ERR;
}

otcrypto_status_t otcrypto_ecdsa_verify_async_finalize(
    const otcrypto_ecc_curve_t *elliptic_curve,
    otcrypto_const_word32_buf_t signature,
    hardened_bool_t *verification_result) {
  if (elliptic_curve == NULL || verification_result == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Select the correct verification operation and finalize it.
  switch (launder32(elliptic_curve->curve_type)) {
    case kOtcryptoEccCurveTypeNistP256:
      HARDENED_CHECK_EQ(elliptic_curve->curve_type,
                        kOtcryptoEccCurveTypeNistP256);
      HARDENED_TRY(p256_signature_length_check(signature.len));
      p256_ecdsa_signature_t *sig_p256 =
          (p256_ecdsa_signature_t *)signature.data;
      return p256_ecdsa_verify_finalize(sig_p256, verification_result);
    case kOtcryptoEccCurveTypeNistP384:
      HARDENED_CHECK_EQ(elliptic_curve->curve_type,
                        kOtcryptoEccCurveTypeNistP384);
      HARDENED_TRY(p384_signature_length_check(signature.len));
      p384_ecdsa_signature_t *sig_p384 =
          (p384_ecdsa_signature_t *)signature.data;
      return p384_ecdsa_verify_finalize(sig_p384, verification_result);
    case kEccCurveTypeBrainpoolP256R1:
      OT_FALLTHROUGH_INTENDED;
    case kOtcryptoEccCurveTypeCustom:
      // TODO: Implement support for other curves.
      return OTCRYPTO_NOT_IMPLEMENTED;
    default:
      return OTCRYPTO_BAD_ARGS;
  }

  // Should never get here.
  HARDENED_TRAP();
  return OTCRYPTO_FATAL_ERR;
}

otcrypto_status_t otcrypto_ecdh_keygen_async_start(
    const otcrypto_ecc_curve_t *elliptic_curve,
    const otcrypto_blinded_key_t *private_key) {
  if (elliptic_curve == NULL || private_key == NULL ||
      private_key->keyblob == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Check the key mode.
  if (launder32(private_key->config.key_mode) != kOtcryptoKeyModeEcdh) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(private_key->config.key_mode, kOtcryptoKeyModeEcdh);

  // Check that the entropy complex is initialized.
  HARDENED_TRY(entropy_complex_check());

  // Select the correct keygen operation and start it.
  switch (launder32(elliptic_curve->curve_type)) {
    case kOtcryptoEccCurveTypeNistP256:
      HARDENED_CHECK_EQ(elliptic_curve->curve_type,
                        kOtcryptoEccCurveTypeNistP256);
      if (launder32(private_key->config.hw_backed) == kHardenedBoolTrue) {
        HARDENED_CHECK_EQ(private_key->config.hw_backed, kHardenedBoolTrue);
        HARDENED_TRY(sideload_key_seed(private_key));
        return p256_sideload_keygen_start();
      } else if (launder32(private_key->config.hw_backed) ==
                 kHardenedBoolFalse) {
        return p256_keygen_start();
      }
      return OTCRYPTO_BAD_ARGS;
    case kOtcryptoEccCurveTypeNistP384:
      HARDENED_CHECK_EQ(elliptic_curve->curve_type,
                        kOtcryptoEccCurveTypeNistP384);
      if (launder32(private_key->config.hw_backed) == kHardenedBoolTrue) {
        HARDENED_CHECK_EQ(private_key->config.hw_backed, kHardenedBoolTrue);
        HARDENED_TRY(sideload_key_seed(private_key));
        return p384_sideload_keygen_start();
      } else if (launder32(private_key->config.hw_backed) ==
                 kHardenedBoolFalse) {
        HARDENED_CHECK_EQ(private_key->config.hw_backed, kHardenedBoolFalse);
        return p384_keygen_start();
      }
      return OTCRYPTO_BAD_ARGS;
    case kEccCurveTypeBrainpoolP256R1:
      OT_FALLTHROUGH_INTENDED;
    case kOtcryptoEccCurveTypeCustom:
      // TODO: Implement support for other curves.
      return OTCRYPTO_NOT_IMPLEMENTED;
    default:
      return OTCRYPTO_BAD_ARGS;
  }

  // Should never get here.
  HARDENED_TRAP();
  return OTCRYPTO_FATAL_ERR;
}

otcrypto_status_t otcrypto_ecdh_keygen_async_finalize(
    const otcrypto_ecc_curve_t *elliptic_curve,
    otcrypto_blinded_key_t *private_key, otcrypto_unblinded_key_t *public_key) {
  // Check for any NULL pointers.
  if (elliptic_curve == NULL || private_key == NULL || public_key == NULL ||
      private_key->keyblob == NULL || public_key->key == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Check the key modes.
  if (launder32(public_key->key_mode) != kOtcryptoKeyModeEcdh ||
      launder32(private_key->config.key_mode) != kOtcryptoKeyModeEcdh) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(public_key->key_mode, kOtcryptoKeyModeEcdh);
  HARDENED_CHECK_EQ(private_key->config.key_mode, kOtcryptoKeyModeEcdh);

  // Select the correct keygen operation and finalize it.
  switch (launder32(elliptic_curve->curve_type)) {
    case kOtcryptoEccCurveTypeNistP256:
      HARDENED_CHECK_EQ(elliptic_curve->curve_type,
                        kOtcryptoEccCurveTypeNistP256);
      HARDENED_TRY(internal_p256_keygen_finalize(private_key, public_key));
      break;
    case kOtcryptoEccCurveTypeNistP384:
      HARDENED_CHECK_EQ(elliptic_curve->curve_type,
                        kOtcryptoEccCurveTypeNistP384);
      HARDENED_TRY(internal_p384_keygen_finalize(private_key, public_key));
      break;
    case kEccCurveTypeBrainpoolP256R1:
      OT_FALLTHROUGH_INTENDED;
    case kOtcryptoEccCurveTypeCustom:
      // TODO: Implement support for other curves.
      return OTCRYPTO_NOT_IMPLEMENTED;
    default:
      return OTCRYPTO_BAD_ARGS;
  }

  // Clear the OTBN sideload slot (in case the key was sideloaded).
  return keymgr_sideload_clear_otbn();
}

/**
 * Start an ECDH shared key generation operation for curve P-256.
 *
 * @param private_key Private key for key exchange.
 * @param public_key Public key for key exchange.
 * @return OK or error.
 */
OT_WARN_UNUSED_RESULT
static status_t internal_ecdh_p256_start(
    const otcrypto_blinded_key_t *private_key,
    const otcrypto_unblinded_key_t *public_key) {
  HARDENED_TRY(p256_private_key_length_check(private_key));
  HARDENED_TRY(p256_public_key_length_check(public_key));
  p256_point_t *pk = (p256_point_t *)public_key->key;

  if (launder32(private_key->config.hw_backed) == kHardenedBoolTrue) {
    HARDENED_CHECK_EQ(private_key->config.hw_backed, kHardenedBoolTrue);
    HARDENED_TRY(sideload_key_seed(private_key));
    return p256_sideload_ecdh_start(pk);
  } else if (launder32(private_key->config.hw_backed) == kHardenedBoolFalse) {
    HARDENED_CHECK_EQ(private_key->config.hw_backed, kHardenedBoolFalse);
    p256_masked_scalar_t *sk = (p256_masked_scalar_t *)private_key->keyblob;
    return p256_ecdh_start(sk, pk);
  }

  // Invalid value for `hw_backed`.
  return OTCRYPTO_BAD_ARGS;
}

/**
 * Start an ECDH shared key generation operation for curve P-384.
 *
 * @param private_key Private key for key exchange.
 * @param public_key Public key for key exchange.
 * @return OK or error.
 */
OT_WARN_UNUSED_RESULT
static status_t internal_ecdh_p384_start(
    const otcrypto_blinded_key_t *private_key,
    const otcrypto_unblinded_key_t *public_key) {
  HARDENED_TRY(p384_private_key_length_check(private_key));
  HARDENED_TRY(p384_public_key_length_check(public_key));
  p384_point_t *pk = (p384_point_t *)public_key->key;

  if (launder32(private_key->config.hw_backed) == kHardenedBoolTrue) {
    HARDENED_CHECK_EQ(private_key->config.hw_backed, kHardenedBoolTrue);
    HARDENED_TRY(sideload_key_seed(private_key));
    return p384_sideload_ecdh_start(pk);
  } else if (launder32(private_key->config.hw_backed) == kHardenedBoolFalse) {
    HARDENED_CHECK_EQ(private_key->config.hw_backed, kHardenedBoolFalse);
    p384_masked_scalar_t *sk = (p384_masked_scalar_t *)private_key->keyblob;
    return p384_ecdh_start(sk, pk);
  }

  // Invalid value for `hw_backed`.
  return OTCRYPTO_BAD_ARGS;
}

otcrypto_status_t otcrypto_ecdh_async_start(
    const otcrypto_blinded_key_t *private_key,
    const otcrypto_unblinded_key_t *public_key,
    const otcrypto_ecc_curve_t *elliptic_curve) {
  if (private_key == NULL || public_key == NULL || elliptic_curve == NULL ||
      public_key->key == NULL || private_key->keyblob == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

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
  if (launder32(private_key->config.key_mode) != kOtcryptoKeyModeEcdh ||
      launder32(public_key->key_mode) != kOtcryptoKeyModeEcdh) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(private_key->config.key_mode, kOtcryptoKeyModeEcdh);
  HARDENED_CHECK_EQ(public_key->key_mode, kOtcryptoKeyModeEcdh);

  // Select the correct ECDH operation and start it.
  switch (launder32(elliptic_curve->curve_type)) {
    case kOtcryptoEccCurveTypeNistP256:
      HARDENED_CHECK_EQ(elliptic_curve->curve_type,
                        kOtcryptoEccCurveTypeNistP256);
      HARDENED_TRY(internal_ecdh_p256_start(private_key, public_key));
      return OTCRYPTO_OK;
    case kOtcryptoEccCurveTypeNistP384:
      HARDENED_CHECK_EQ(elliptic_curve->curve_type,
                        kOtcryptoEccCurveTypeNistP384);
      HARDENED_TRY(internal_ecdh_p384_start(private_key, public_key));
      return OTCRYPTO_OK;
    case kEccCurveTypeBrainpoolP256R1:
      OT_FALLTHROUGH_INTENDED;
    case kOtcryptoEccCurveTypeCustom:
      // TODO: Implement support for other curves.
      return OTCRYPTO_NOT_IMPLEMENTED;
    default:
      return OTCRYPTO_BAD_ARGS;
  }

  // Should never get here.
  HARDENED_TRAP();
  return OTCRYPTO_FATAL_ERR;
}

/**
 * Finish an ECDH shared key generation operation for curve P-256.
 *
 * @param[out] shared_secret Resulting shared secret.
 * @return OK or error.
 */
OT_WARN_UNUSED_RESULT
static status_t internal_ecdh_p256_finalize(
    otcrypto_blinded_key_t *shared_secret) {
  if (launder32(shared_secret->config.hw_backed) != kHardenedBoolFalse) {
    // Shared keys cannot be sideloaded because they are software-generated.
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(shared_secret->config.hw_backed, kHardenedBoolFalse);

  if (shared_secret->keyblob == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

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
  HARDENED_TRY(p256_ecdh_finalize(&ss));

  keyblob_from_shares(ss.share0, ss.share1, shared_secret->config,
                      shared_secret->keyblob);

  // Set the checksum.
  shared_secret->checksum = integrity_blinded_checksum(shared_secret);

  // Clear the OTBN sideload slot (in case the seed was sideloaded).
  return keymgr_sideload_clear_otbn();
}

/**
 * Finish an ECDH shared key generation operation for curve P-384.
 *
 * @param[out] shared_secret Resulting shared secret.
 * @return OK or error.
 */
OT_WARN_UNUSED_RESULT
static status_t internal_ecdh_p384_finalize(
    otcrypto_blinded_key_t *shared_secret) {
  if (launder32(shared_secret->config.hw_backed) != kHardenedBoolFalse) {
    // Shared keys cannot be sideloaded because they are software-generated.
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(shared_secret->config.hw_backed, kHardenedBoolFalse);

  if (shared_secret->keyblob == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  if (launder32(shared_secret->config.key_length) != kP384CoordBytes) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(shared_secret->config.key_length, kP384CoordBytes);

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
  p384_ecdh_shared_key_t ss;
  HARDENED_TRY(p384_ecdh_finalize(&ss));

  keyblob_from_shares(ss.share0, ss.share1, shared_secret->config,
                      shared_secret->keyblob);

  // Set the checksum.
  shared_secret->checksum = integrity_blinded_checksum(shared_secret);

  // Clear the OTBN sideload slot (in case the seed was sideloaded).
  return keymgr_sideload_clear_otbn();
}

otcrypto_status_t otcrypto_ecdh_async_finalize(
    const otcrypto_ecc_curve_t *elliptic_curve,
    otcrypto_blinded_key_t *shared_secret) {
  if (shared_secret == NULL || elliptic_curve == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Select the correct ECDH operation and finalize it.
  switch (launder32(elliptic_curve->curve_type)) {
    case kOtcryptoEccCurveTypeNistP256:
      HARDENED_CHECK_EQ(elliptic_curve->curve_type,
                        kOtcryptoEccCurveTypeNistP256);
      HARDENED_TRY(internal_ecdh_p256_finalize(shared_secret));
      break;
    case kOtcryptoEccCurveTypeNistP384:
      HARDENED_CHECK_EQ(elliptic_curve->curve_type,
                        kOtcryptoEccCurveTypeNistP384);
      HARDENED_TRY(internal_ecdh_p384_finalize(shared_secret));
      break;
    case kEccCurveTypeBrainpoolP256R1:
      OT_FALLTHROUGH_INTENDED;
    case kOtcryptoEccCurveTypeCustom:
      // TODO: Implement support for other curves.
      return OTCRYPTO_NOT_IMPLEMENTED;
    default:
      return OTCRYPTO_BAD_ARGS;
  }

  // Clear the OTBN sideload slot (in case the key was sideloaded).
  return keymgr_sideload_clear_otbn();
}

otcrypto_status_t otcrypto_ed25519_keygen_async_start(
    const otcrypto_blinded_key_t *private_key) {
  // TODO: Ed25519 is not yet implemented.
  return OTCRYPTO_NOT_IMPLEMENTED;
}

otcrypto_status_t otcrypto_ed25519_keygen_async_finalize(
    otcrypto_blinded_key_t *private_key, otcrypto_unblinded_key_t *public_key) {
  // TODO: Ed25519 is not yet implemented.
  return OTCRYPTO_NOT_IMPLEMENTED;
}

otcrypto_status_t otcrypto_ed25519_sign_async_start(
    const otcrypto_blinded_key_t *private_key,
    otcrypto_const_byte_buf_t input_message,
    otcrypto_eddsa_sign_mode_t sign_mode, otcrypto_word32_buf_t signature) {
  // TODO: Ed25519 is not yet implemented.
  return OTCRYPTO_NOT_IMPLEMENTED;
}

otcrypto_status_t otcrypto_ed25519_sign_async_finalize(
    otcrypto_word32_buf_t signature) {
  // TODO: Ed25519 is not yet implemented.
  return OTCRYPTO_NOT_IMPLEMENTED;
}

otcrypto_status_t otcrypto_ed25519_verify_async_start(
    const otcrypto_unblinded_key_t *public_key,
    otcrypto_const_byte_buf_t input_message,
    otcrypto_eddsa_sign_mode_t sign_mode,
    otcrypto_const_word32_buf_t signature) {
  // TODO: Ed25519 is not yet implemented.
  return OTCRYPTO_NOT_IMPLEMENTED;
}

otcrypto_status_t otcrypto_ed25519_verify_async_finalize(
    hardened_bool_t *verification_result) {
  // TODO: Ed25519 is not yet implemented.
  return OTCRYPTO_NOT_IMPLEMENTED;
}

otcrypto_status_t otcrypto_x25519_keygen_async_start(
    const otcrypto_blinded_key_t *private_key) {
  // TODO: X25519 is not yet implemented.
  return OTCRYPTO_NOT_IMPLEMENTED;
}

otcrypto_status_t otcrypto_x25519_keygen_async_finalize(
    otcrypto_blinded_key_t *private_key, otcrypto_unblinded_key_t *public_key) {
  // TODO: X25519 is not yet implemented.
  return OTCRYPTO_NOT_IMPLEMENTED;
}

otcrypto_status_t otcrypto_x25519_async_start(
    const otcrypto_blinded_key_t *private_key,
    const otcrypto_unblinded_key_t *public_key) {
  // TODO: X25519 is not yet implemented.
  return OTCRYPTO_NOT_IMPLEMENTED;
}

otcrypto_status_t otcrypto_x25519_async_finalize(
    otcrypto_blinded_key_t *shared_secret) {
  // TODO: X25519 is not yet implemented.
  return OTCRYPTO_NOT_IMPLEMENTED;
}
