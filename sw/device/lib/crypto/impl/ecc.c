// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/include/ecc.h"

#include "sw/device/lib/crypto/drivers/entropy.h"
#include "sw/device/lib/crypto/drivers/hmac.h"
#include "sw/device/lib/crypto/impl/ecc/ecdh_p256.h"
#include "sw/device/lib/crypto/impl/ecc/ecdsa_p256.h"
#include "sw/device/lib/crypto/impl/integrity.h"
#include "sw/device/lib/crypto/impl/keyblob.h"
#include "sw/device/lib/crypto/include/datatypes.h"

// Module ID for status codes.
#define MODULE_ID MAKE_MODULE_ID('e', 'c', 'c')

crypto_status_t otcrypto_ecdsa_keygen(const ecc_curve_t *elliptic_curve,
                                      crypto_blinded_key_t *private_key,
                                      ecc_public_key_t *public_key) {
  const crypto_key_config_t config = private_key->config;
  HARDENED_TRY(otcrypto_ecdsa_keygen_async_start(elliptic_curve, &config));
  return otcrypto_ecdsa_keygen_async_finalize(elliptic_curve, private_key,
                                              public_key);
}

crypto_status_t otcrypto_ecdsa_sign(const crypto_blinded_key_t *private_key,
                                    crypto_const_byte_buf_t input_message,
                                    const ecc_curve_t *elliptic_curve,
                                    const ecc_signature_t *signature) {
  HARDENED_TRY(otcrypto_ecdsa_sign_async_start(private_key, input_message,
                                               elliptic_curve));
  return otcrypto_ecdsa_sign_async_finalize(elliptic_curve, signature);
}

crypto_status_t otcrypto_ecdsa_verify(const ecc_public_key_t *public_key,
                                      crypto_const_byte_buf_t input_message,
                                      const ecc_signature_t *signature,
                                      const ecc_curve_t *elliptic_curve,
                                      hardened_bool_t *verification_result) {
  HARDENED_TRY(otcrypto_ecdsa_verify_async_start(public_key, input_message,
                                                 signature, elliptic_curve));
  return otcrypto_ecdsa_verify_async_finalize(elliptic_curve, signature,
                                              verification_result);
}

crypto_status_t otcrypto_ecdh_keygen(const ecc_curve_t *elliptic_curve,
                                     crypto_blinded_key_t *private_key,
                                     ecc_public_key_t *public_key) {
  HARDENED_TRY(
      otcrypto_ecdh_keygen_async_start(elliptic_curve, &private_key->config));
  return otcrypto_ecdh_keygen_async_finalize(elliptic_curve, private_key,
                                             public_key);
}

crypto_status_t otcrypto_ecdh(const crypto_blinded_key_t *private_key,
                              const ecc_public_key_t *public_key,
                              const ecc_curve_t *elliptic_curve,
                              crypto_blinded_key_t *shared_secret) {
  HARDENED_TRY(
      otcrypto_ecdh_async_start(private_key, public_key, elliptic_curve));
  return otcrypto_ecdh_async_finalize(elliptic_curve, shared_secret);
}

crypto_status_t otcrypto_ed25519_keygen(crypto_blinded_key_t *private_key,
                                        crypto_unblinded_key_t *public_key) {
  // TODO: Ed25519 is not yet implemented.
  return OTCRYPTO_NOT_IMPLEMENTED;
}

crypto_status_t otcrypto_ed25519_sign(const crypto_blinded_key_t *private_key,
                                      crypto_const_byte_buf_t input_message,
                                      eddsa_sign_mode_t sign_mode,
                                      const ecc_signature_t *signature) {
  // TODO: Ed25519 is not yet implemented.
  return OTCRYPTO_NOT_IMPLEMENTED;
}

crypto_status_t otcrypto_ed25519_verify(
    const crypto_unblinded_key_t *public_key,
    crypto_const_byte_buf_t input_message, eddsa_sign_mode_t sign_mode,
    const ecc_signature_t *signature, hardened_bool_t *verification_result) {
  // TODO: Ed25519 is not yet implemented.
  return OTCRYPTO_NOT_IMPLEMENTED;
}

crypto_status_t otcrypto_x25519_keygen(crypto_blinded_key_t *private_key,
                                       crypto_unblinded_key_t *public_key) {
  // TODO: Connect X25519 operations to API.
  return OTCRYPTO_NOT_IMPLEMENTED;
}

crypto_status_t otcrypto_x25519(const crypto_blinded_key_t *private_key,
                                const crypto_unblinded_key_t *public_key,
                                crypto_blinded_key_t *shared_secret) {
  // TODO: Connect X25519 operations to API.
  return OTCRYPTO_NOT_IMPLEMENTED;
}

/**
 * Consistency checks for caller-provided private key configurations.
 *
 * This check ensures:
 *   - The key length in the configuration matches the given curve
 *   - The key mode matches expectations.
 *
 * @param elliptic_curve Curve for which key is intended.
 * @param config Private key configuration.
 * @param expected_mode Expected key mode.
 * @returns OK if the check passes, BAD_ARGS otherwise.
 */
static status_t key_config_check(const ecc_curve_t *elliptic_curve,
                                 const crypto_key_config_t *config,
                                 key_mode_t expected_mode) {
  // Check the key mode.
  if (config->key_mode != expected_mode) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(config->key_mode, expected_mode);

  // Check the key length.
  switch (launder32(elliptic_curve->curve_type)) {
    case kEccCurveTypeNistP256:
      HARDENED_CHECK_EQ(elliptic_curve->curve_type, kEccCurveTypeNistP256);
      if (launder32(config->key_length) != kP256ScalarBytes) {
        return OTCRYPTO_BAD_ARGS;
      }
      HARDENED_CHECK_EQ(config->key_length, kP256ScalarBytes);
      return OTCRYPTO_OK;
    case kEccCurveTypeNistP384:
      OT_FALLTHROUGH_INTENDED;
    case kEccCurveTypeBrainpoolP256R1:
      OT_FALLTHROUGH_INTENDED;
    case kEccCurveTypeCustom:
      // TODO: Implement support for other curves.
      return OTCRYPTO_NOT_IMPLEMENTED;
    default:
      // Unrecognized curve type.
      return OTCRYPTO_BAD_ARGS;
  }

  // Should never get here.
  HARDENED_TRAP();
  return OTCRYPTO_FATAL_ERR;
}

crypto_status_t otcrypto_ecdsa_keygen_async_start(
    const ecc_curve_t *elliptic_curve, const crypto_key_config_t *config) {
  if (elliptic_curve == NULL || config == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  if (config->hw_backed != kHardenedBoolFalse) {
    // TODO: Implement support for sideloaded keys.
    return OTCRYPTO_NOT_IMPLEMENTED;
  }

  // Check the key configuration.
  HARDENED_TRY(key_config_check(elliptic_curve, config, kKeyModeEcdsa));

  // Check that the entropy complex is initialized.
  HARDENED_TRY(entropy_complex_check());

  // Select the correct keygen operation and start it.
  switch (launder32(elliptic_curve->curve_type)) {
    case kEccCurveTypeNistP256:
      HARDENED_CHECK_EQ(elliptic_curve->curve_type, kEccCurveTypeNistP256);
      HARDENED_TRY(ecdsa_p256_keygen_start());
      return OTCRYPTO_OK;
    case kEccCurveTypeNistP384:
      OT_FALLTHROUGH_INTENDED;
    case kEccCurveTypeBrainpoolP256R1:
      OT_FALLTHROUGH_INTENDED;
    case kEccCurveTypeCustom:
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
 * @param private_key Private key struct to check.
 * @return OK if the lengths are correct or BAD_ARGS otherwise.
 */
static status_t p256_private_key_length_check(
    const crypto_blinded_key_t *private_key) {
  if (private_key->config.hw_backed != kHardenedBoolFalse) {
    // TODO: Implement support for sideloaded keys.
    return OTCRYPTO_NOT_IMPLEMENTED;
  }

  // Since sideloaded keys are not supported, the keyblob may not be NULL.
  if (private_key->keyblob == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Check the single-share length.
  if (keyblob_share_num_words(private_key->config) !=
      kP256MaskedScalarShareWords) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Check the keyblob length.
  if (launder32(private_key->keyblob_length) !=
      keyblob_num_words(private_key->config) * sizeof(uint32_t)) {
    return OTCRYPTO_BAD_ARGS;
  }

  return OTCRYPTO_OK;
}

/**
 * Check the lengths of public keys for curve P-256.
 *
 * Checks the length of caller-allocated buffers for a P-256 public key. This
 * function may be used for both ECDSA and ECDH keys, since the key structure
 * is the same.
 *
 * @param public_key Public key struct to check.
 * @return OK if the lengths are correct or BAD_ARGS otherwise.
 */
static status_t p256_public_key_length_check(
    const ecc_public_key_t *public_key) {
  if (launder32(public_key->x.key_length) != kP256CoordBytes ||
      launder32(public_key->y.key_length != kP256CoordBytes)) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(public_key->x.key_length, kP256CoordBytes);
  HARDENED_CHECK_EQ(public_key->y.key_length, kP256CoordBytes);

  return OTCRYPTO_OK;
}

/**
 * Finalize an ECDSA key generation operation for curve P-256.
 *
 * This function assumes that space is already allocated for all key material
 * and that the length parameters on the structs are set accordingly, in the
 * same way as for `otcrypto_ecdsa_keygen_async_finalize`.
 *
 * @param[out] private_key Private key to populate.
 * @param[out] public_key Public key to populate.
 * @return OK or error.
 */
static status_t internal_ecdsa_p256_keygen_finalize(
    crypto_blinded_key_t *private_key, ecc_public_key_t *public_key) {
  // Check the lengths of caller-allocated buffers.
  HARDENED_TRY(p256_private_key_length_check(private_key));
  HARDENED_TRY(p256_public_key_length_check(public_key));

  // Note: This operation wipes DMEM after retrieving the keys, so if an error
  // occurs after this point then the keys would be unrecoverable. This should
  // be the last potentially error-causing line before returning to the caller.
  p256_masked_scalar_t sk;
  p256_point_t pk;
  HARDENED_TRY(ecdsa_p256_keygen_finalize(&sk, &pk));

  // Prepare the private key.
  keyblob_from_shares(sk.share0, sk.share1, private_key->config,
                      private_key->keyblob);
  private_key->checksum = integrity_blinded_checksum(private_key);

  // Prepare the public key.
  memcpy(public_key->x.key, pk.x, kP256CoordBytes);
  memcpy(public_key->y.key, pk.y, kP256CoordBytes);
  public_key->x.checksum = integrity_unblinded_checksum(&public_key->x);
  public_key->y.checksum = integrity_unblinded_checksum(&public_key->y);

  return OTCRYPTO_OK;
}

/**
 * Consistency checks for caller-provided public keys.
 *
 * Checks for NULL pointers within the struct and ensures that the key mode is
 * as expected. Does not check integrity or length.
 *
 * @param public_key Caller-provided public key struct.
 * @param expected_mode Expected key mode.
 */
static status_t ecc_public_key_check(const ecc_public_key_t *public_key,
                                     const key_mode_t expected_mode) {
  // Check for null pointers.
  if (public_key->x.key == NULL || public_key->y.key == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Check the mode.
  if (public_key->x.key_mode != expected_mode ||
      public_key->y.key_mode != expected_mode) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(public_key->x.key_mode, expected_mode);
  HARDENED_CHECK_EQ(public_key->y.key_mode, expected_mode);

  return OTCRYPTO_OK;
}

crypto_status_t otcrypto_ecdsa_keygen_async_finalize(
    const ecc_curve_t *elliptic_curve, crypto_blinded_key_t *private_key,
    ecc_public_key_t *public_key) {
  // Check for any NULL pointers.
  if (elliptic_curve == NULL || private_key == NULL || public_key == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Consistency check for the public key.
  HARDENED_TRY(ecc_public_key_check(public_key, kKeyModeEcdsa));

  // Consistency check for the private key configuration.
  HARDENED_TRY(
      key_config_check(elliptic_curve, &private_key->config, kKeyModeEcdsa));

  // Select the correct keygen operation and finalize it.
  switch (launder32(elliptic_curve->curve_type)) {
    case kEccCurveTypeNistP256:
      HARDENED_CHECK_EQ(elliptic_curve->curve_type, kEccCurveTypeNistP256);
      HARDENED_TRY(
          internal_ecdsa_p256_keygen_finalize(private_key, public_key));
      return OTCRYPTO_OK;
    case kEccCurveTypeNistP384:
      OT_FALLTHROUGH_INTENDED;
    case kEccCurveTypeBrainpoolP256R1:
      OT_FALLTHROUGH_INTENDED;
    case kEccCurveTypeCustom:
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
 * Start an ECDSA signature generation operation for curve P-256.
 *
 * @param private_key Private key to sign with.
 * @param input_message Message to sign.
 * @return OK or error.
 */
static status_t internal_ecdsa_p256_sign_start(
    const crypto_blinded_key_t *private_key,
    crypto_const_byte_buf_t input_message) {
  if (private_key->config.hw_backed != kHardenedBoolFalse) {
    // TODO: Implement support for sideloaded keys.
    return OTCRYPTO_NOT_IMPLEMENTED;
  }

  // Check the private key size.
  HARDENED_TRY(p256_private_key_length_check(private_key));

  // Get pointers to the individual shares within the blinded key.
  uint32_t *share0;
  uint32_t *share1;
  HARDENED_TRY(keyblob_to_shares(private_key, &share0, &share1));

  // Copy the shares into a P256-specific struct.
  p256_masked_scalar_t sk;
  memcpy(sk.share0, share0, sizeof(sk.share0));
  memcpy(sk.share1, share1, sizeof(sk.share1));

  // Get the SHA256 digest of the message.
  hmac_sha_init();
  hmac_update(input_message.data, input_message.len);
  hmac_digest_t digest;
  hmac_final(&digest);

  // Start the asynchronous signature-generation routine.
  return ecdsa_p256_sign_start(digest.digest, &sk);
}

crypto_status_t otcrypto_ecdsa_sign_async_start(
    const crypto_blinded_key_t *private_key,
    crypto_const_byte_buf_t input_message, const ecc_curve_t *elliptic_curve) {
  if (private_key == NULL || elliptic_curve == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  if (input_message.data == NULL && input_message.len != 0) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Check the integrity of the private key.
  if (integrity_blinded_key_check(private_key) != kHardenedBoolTrue) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Check the private key configuration.
  HARDENED_TRY(
      key_config_check(elliptic_curve, &private_key->config, kKeyModeEcdsa));

  // Check that the entropy complex is initialized.
  HARDENED_TRY(entropy_complex_check());

  // Select the correct signing operation and start it.
  switch (launder32(elliptic_curve->curve_type)) {
    case kEccCurveTypeNistP256:
      HARDENED_CHECK_EQ(elliptic_curve->curve_type, kEccCurveTypeNistP256);
      HARDENED_TRY(internal_ecdsa_p256_sign_start(private_key, input_message));
      return OTCRYPTO_OK;
    case kEccCurveTypeNistP384:
      OT_FALLTHROUGH_INTENDED;
    case kEccCurveTypeBrainpoolP256R1:
      OT_FALLTHROUGH_INTENDED;
    case kEccCurveTypeCustom:
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
 * Finalize an ECDSA signature generation operation for curve P-256.
 *
 * This function assumes that space is already allocated for the signature and
 * that the length parameters on the struct are set accordingly, in the same
 * way as for `otcrypto_ecdsa_sign_async_finalize`.
 *
 * @param[out] signature Caller-allocated buffer for the signature.
 * @return OK or error.
 */
static status_t internal_ecdsa_p256_sign_finalize(
    const ecc_signature_t *signature) {
  // Check the lengths of caller-allocated buffers.
  if (signature->len_r != kP256ScalarBytes ||
      signature->len_s != kP256ScalarBytes) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(signature->len_r, kP256ScalarBytes);
  HARDENED_CHECK_EQ(signature->len_s, kP256ScalarBytes);

  // Note: This operation wipes DMEM, so if an error occurs after this point
  // then the singature would be unrecoverable. This should be the last
  // potentially error-causing line before returning to the caller.
  ecdsa_p256_signature_t sig;
  HARDENED_TRY(ecdsa_p256_sign_finalize(&sig));

  // Copy the signature to the caller.
  memcpy(signature->r, sig.r, kP256ScalarBytes);
  memcpy(signature->s, sig.s, kP256ScalarBytes);

  return OTCRYPTO_OK;
}

crypto_status_t otcrypto_ecdsa_sign_async_finalize(
    const ecc_curve_t *elliptic_curve, const ecc_signature_t *signature) {
  if (elliptic_curve == NULL || signature == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Select the correct signing operation and finalize it.
  switch (launder32(elliptic_curve->curve_type)) {
    case kEccCurveTypeNistP256:
      HARDENED_CHECK_EQ(elliptic_curve->curve_type, kEccCurveTypeNistP256);
      HARDENED_TRY(internal_ecdsa_p256_sign_finalize(signature));
      return OTCRYPTO_OK;
    case kEccCurveTypeNistP384:
      OT_FALLTHROUGH_INTENDED;
    case kEccCurveTypeBrainpoolP256R1:
      OT_FALLTHROUGH_INTENDED;
    case kEccCurveTypeCustom:
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
 * Start an ECDSA signature verification operation for curve P-256.
 *
 * @param public_key Public key to check against.
 * @param input_message Message to check against.
 * @param signature Signature to verify.
 * @return OK or error.
 */
static status_t internal_ecdsa_p256_verify_start(
    const ecc_public_key_t *public_key, crypto_const_byte_buf_t input_message,
    const ecc_signature_t *signature) {
  // Check the public key size.
  HARDENED_TRY(p256_public_key_length_check(public_key));

  // Copy the public key into a P256-specific struct.
  p256_point_t pk;
  memcpy(pk.x, public_key->x.key, sizeof(pk.x));
  memcpy(pk.y, public_key->y.key, sizeof(pk.y));

  // Check the signature lengths.
  if (signature->len_r != kP256ScalarBytes ||
      signature->len_s != kP256ScalarBytes) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(signature->len_r, kP256ScalarBytes);
  HARDENED_CHECK_EQ(signature->len_s, kP256ScalarBytes);

  // Copy the signature into a P256-specific struct.
  ecdsa_p256_signature_t sig;
  memcpy(sig.r, signature->r, sizeof(sig.r));
  memcpy(sig.s, signature->s, sizeof(sig.s));

  // Get the SHA256 digest of the message.
  hmac_sha_init();
  hmac_update(input_message.data, input_message.len);
  hmac_digest_t digest;
  hmac_final(&digest);

  // Start the asynchronous signature-verification routine.
  return ecdsa_p256_verify_start(&sig, digest.digest, &pk);
}

crypto_status_t otcrypto_ecdsa_verify_async_start(
    const ecc_public_key_t *public_key, crypto_const_byte_buf_t input_message,
    const ecc_signature_t *signature, const ecc_curve_t *elliptic_curve) {
  if (public_key == NULL || elliptic_curve == NULL || signature == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  if (input_message.data == NULL && input_message.len != 0) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Consistency check for the public key.
  HARDENED_TRY(ecc_public_key_check(public_key, kKeyModeEcdsa));

  // Check the integrity of the public key.
  if (launder32(integrity_unblinded_key_check(&public_key->x)) !=
          kHardenedBoolTrue ||
      launder32(integrity_unblinded_key_check(&public_key->y)) !=
          kHardenedBoolTrue) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(integrity_unblinded_key_check(&public_key->x),
                    kHardenedBoolTrue);
  HARDENED_CHECK_EQ(integrity_unblinded_key_check(&public_key->y),
                    kHardenedBoolTrue);

  // Select the correct verification operation and start it.
  switch (launder32(elliptic_curve->curve_type)) {
    case kEccCurveTypeNistP256:
      HARDENED_CHECK_EQ(elliptic_curve->curve_type, kEccCurveTypeNistP256);
      HARDENED_TRY(internal_ecdsa_p256_verify_start(public_key, input_message,
                                                    signature));
      return OTCRYPTO_OK;
    case kEccCurveTypeNistP384:
      OT_FALLTHROUGH_INTENDED;
    case kEccCurveTypeBrainpoolP256R1:
      OT_FALLTHROUGH_INTENDED;
    case kEccCurveTypeCustom:
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
 * Finalize an ECDSA signature verification operation for curve P-256.
 *
 * @param verification_result Whether the signature passed verification.
 * @return OK or error.
 */
static status_t internal_ecdsa_p256_verify_finalize(
    const ecc_signature_t *signature, hardened_bool_t *verification_result) {
  // Check the signature lengths.
  if (signature->len_r != kP256ScalarBytes ||
      signature->len_s != kP256ScalarBytes) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(signature->len_r, kP256ScalarBytes);
  HARDENED_CHECK_EQ(signature->len_s, kP256ScalarBytes);

  // Copy the signature into a P256-specific struct.
  ecdsa_p256_signature_t sig;
  memcpy(sig.r, signature->r, sizeof(sig.r));
  memcpy(sig.s, signature->s, sizeof(sig.s));

  // Retrieve the result of the verification operation.
  return ecdsa_p256_verify_finalize(&sig, verification_result);
}

crypto_status_t otcrypto_ecdsa_verify_async_finalize(
    const ecc_curve_t *elliptic_curve, const ecc_signature_t *signature,
    hardened_bool_t *verification_result) {
  if (elliptic_curve == NULL || verification_result == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Select the correct verification operation and finalize it.
  switch (launder32(elliptic_curve->curve_type)) {
    case kEccCurveTypeNistP256:
      HARDENED_CHECK_EQ(elliptic_curve->curve_type, kEccCurveTypeNistP256);
      HARDENED_TRY(
          internal_ecdsa_p256_verify_finalize(signature, verification_result));
      return OTCRYPTO_OK;
    case kEccCurveTypeNistP384:
      OT_FALLTHROUGH_INTENDED;
    case kEccCurveTypeBrainpoolP256R1:
      OT_FALLTHROUGH_INTENDED;
    case kEccCurveTypeCustom:
      // TODO: Implement support for other curves.
      return OTCRYPTO_NOT_IMPLEMENTED;
    default:
      return OTCRYPTO_BAD_ARGS;
  }

  // Should never get here.
  HARDENED_TRAP();
  return OTCRYPTO_FATAL_ERR;
}

crypto_status_t otcrypto_ecdh_keygen_async_start(
    const ecc_curve_t *elliptic_curve, const crypto_key_config_t *config) {
  if (elliptic_curve == NULL || config == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  if (config->hw_backed != kHardenedBoolFalse) {
    // TODO: Implement support for sideloaded keys.
    return OTCRYPTO_NOT_IMPLEMENTED;
  }

  // Check the key configuration.
  HARDENED_TRY(key_config_check(elliptic_curve, config, kKeyModeEcdh));

  // Check that the entropy complex is initialized.
  HARDENED_TRY(entropy_complex_check());

  // Select the correct keygen operation and start it.
  switch (launder32(elliptic_curve->curve_type)) {
    case kEccCurveTypeNistP256:
      HARDENED_CHECK_EQ(elliptic_curve->curve_type, kEccCurveTypeNistP256);
      HARDENED_TRY(ecdh_p256_keypair_start());
      return OTCRYPTO_OK;
    case kEccCurveTypeNistP384:
      OT_FALLTHROUGH_INTENDED;
    case kEccCurveTypeBrainpoolP256R1:
      OT_FALLTHROUGH_INTENDED;
    case kEccCurveTypeCustom:
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
 * Finalize an ECDH keypair generation operation for curve P-256.
 *
 * This function assumes that space is already allocated for all key material
 * and that the length parameters on the structs are set accordingly, in the
 * same way as for `otcrypto_ecdh_keygen_async_finalize`.
 *
 * @param[out] private_key Private key to populate.
 * @param[out] public_key Public key to populate.
 * @return OK or error.
 */
static status_t internal_ecdh_p256_keygen_finalize(
    crypto_blinded_key_t *private_key, ecc_public_key_t *public_key) {
  if (private_key->config.hw_backed != kHardenedBoolFalse) {
    // TODO: Implement support for sideloaded keys.
    return OTCRYPTO_NOT_IMPLEMENTED;
  }

  // Check the lengths of caller-allocated buffers.
  HARDENED_TRY(p256_private_key_length_check(private_key));
  HARDENED_TRY(p256_public_key_length_check(public_key));

  // Note: This operation wipes DMEM after retrieving the keys, so if an error
  // occurs after this point then the keys would be unrecoverable. This should
  // be the last potentially error-causing line before returning to the caller.
  p256_masked_scalar_t sk;
  p256_point_t pk;
  HARDENED_TRY(ecdh_p256_keypair_finalize(&sk, &pk));

  // Prepare the private key.
  keyblob_from_shares(sk.share0, sk.share1, private_key->config,
                      private_key->keyblob);
  private_key->checksum = integrity_blinded_checksum(private_key);

  // Prepare the public key.
  memcpy(public_key->x.key, pk.x, kP256CoordBytes);
  memcpy(public_key->y.key, pk.y, kP256CoordBytes);
  public_key->x.checksum = integrity_unblinded_checksum(&public_key->x);
  public_key->y.checksum = integrity_unblinded_checksum(&public_key->y);

  return OTCRYPTO_OK;
}

crypto_status_t otcrypto_ecdh_keygen_async_finalize(
    const ecc_curve_t *elliptic_curve, crypto_blinded_key_t *private_key,
    ecc_public_key_t *public_key) {
  // Check for any NULL pointers.
  if (elliptic_curve == NULL || private_key == NULL || public_key == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Consistency check for the public key.
  HARDENED_TRY(ecc_public_key_check(public_key, kKeyModeEcdh));

  // Consistency check for the private key configuration.
  HARDENED_TRY(
      key_config_check(elliptic_curve, &private_key->config, kKeyModeEcdh));

  // Select the correct keygen operation and finalize it.
  switch (launder32(elliptic_curve->curve_type)) {
    case kEccCurveTypeNistP256:
      HARDENED_CHECK_EQ(elliptic_curve->curve_type, kEccCurveTypeNistP256);
      HARDENED_TRY(internal_ecdh_p256_keygen_finalize(private_key, public_key));
      return OTCRYPTO_OK;
    case kEccCurveTypeNistP384:
      OT_FALLTHROUGH_INTENDED;
    case kEccCurveTypeBrainpoolP256R1:
      OT_FALLTHROUGH_INTENDED;
    case kEccCurveTypeCustom:
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
 * Start an ECDH shared key generation operation for curve P-256.
 *
 * @param private_key Private key for key exchange.
 * @param public_key Public key for key exchange.
 * @return OK or error.
 */
static status_t internal_ecdh_p256_start(
    const crypto_blinded_key_t *private_key,
    const ecc_public_key_t *public_key) {
  if (private_key->config.hw_backed != kHardenedBoolFalse) {
    // TODO: Implement support for sideloaded keys.
    return OTCRYPTO_NOT_IMPLEMENTED;
  }

  // Check the private key size.
  HARDENED_TRY(p256_private_key_length_check(private_key));

  // Get pointers to the individual shares within the blinded key.
  uint32_t *share0;
  uint32_t *share1;
  HARDENED_TRY(keyblob_to_shares(private_key, &share0, &share1));

  // Copy the shares into a P256-specific struct.
  p256_masked_scalar_t sk;
  memcpy(sk.share0, share0, sizeof(sk.share0));
  memcpy(sk.share1, share1, sizeof(sk.share1));

  // Check the public key size.
  HARDENED_TRY(p256_public_key_length_check(public_key));

  // Copy the public key into a P256-specific struct.
  p256_point_t pk;
  memcpy(pk.x, public_key->x.key, sizeof(pk.x));
  memcpy(pk.y, public_key->y.key, sizeof(pk.y));

  // Check the lengths of caller-allocated buffers.
  HARDENED_TRY(p256_private_key_length_check(private_key));
  HARDENED_TRY(p256_public_key_length_check(public_key));

  // Note: This operation wipes DMEM after retrieving the key, so if an error
  // occurs after this point then the keys would be unrecoverable. This should
  // be the last potentially error-causing line before returning to the caller.
  return ecdh_p256_shared_key_start(&sk, &pk);
}

crypto_status_t otcrypto_ecdh_async_start(
    const crypto_blinded_key_t *private_key, const ecc_public_key_t *public_key,
    const ecc_curve_t *elliptic_curve) {
  if (private_key == NULL || public_key == NULL || elliptic_curve == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Check the integrity of the private key.
  if (integrity_blinded_key_check(private_key) != kHardenedBoolTrue) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Check the private key configuration.
  HARDENED_TRY(
      key_config_check(elliptic_curve, &private_key->config, kKeyModeEcdh));

  // Select the correct ECDH operation and start it.
  switch (launder32(elliptic_curve->curve_type)) {
    case kEccCurveTypeNistP256:
      HARDENED_CHECK_EQ(elliptic_curve->curve_type, kEccCurveTypeNistP256);
      HARDENED_TRY(internal_ecdh_p256_start(private_key, public_key));
      return OTCRYPTO_OK;
    case kEccCurveTypeNistP384:
      OT_FALLTHROUGH_INTENDED;
    case kEccCurveTypeBrainpoolP256R1:
      OT_FALLTHROUGH_INTENDED;
    case kEccCurveTypeCustom:
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
static status_t internal_ecdh_p256_finalize(
    crypto_blinded_key_t *shared_secret) {
  if (shared_secret->config.hw_backed != kHardenedBoolFalse) {
    // Shared keys cannot be sideloaded because they are software-generated.
    return OTCRYPTO_BAD_ARGS;
  }

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
  ecdh_p256_shared_key_t ss;
  HARDENED_TRY(ecdh_p256_shared_key_finalize(&ss));

  keyblob_from_shares(ss.share0, ss.share1, shared_secret->config,
                      shared_secret->keyblob);

  // Set the checksum.
  shared_secret->checksum = integrity_blinded_checksum(shared_secret);

  return OTCRYPTO_OK;
}

crypto_status_t otcrypto_ecdh_async_finalize(
    const ecc_curve_t *elliptic_curve, crypto_blinded_key_t *shared_secret) {
  if (shared_secret == NULL || elliptic_curve == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Select the correct ECDH operation and finalize it.
  switch (launder32(elliptic_curve->curve_type)) {
    case kEccCurveTypeNistP256:
      HARDENED_CHECK_EQ(elliptic_curve->curve_type, kEccCurveTypeNistP256);
      HARDENED_TRY(internal_ecdh_p256_finalize(shared_secret));
      return OTCRYPTO_OK;
    case kEccCurveTypeNistP384:
      OT_FALLTHROUGH_INTENDED;
    case kEccCurveTypeBrainpoolP256R1:
      OT_FALLTHROUGH_INTENDED;
    case kEccCurveTypeCustom:
      // TODO: Implement support for other curves.
      return OTCRYPTO_NOT_IMPLEMENTED;
    default:
      return OTCRYPTO_BAD_ARGS;
  }

  // Should never get here.
  HARDENED_TRAP();
  return OTCRYPTO_FATAL_ERR;
}

crypto_status_t otcrypto_ed25519_keygen_async_start(
    const crypto_key_config_t *config) {
  // TODO: Ed25519 is not yet implemented.
  return OTCRYPTO_NOT_IMPLEMENTED;
}

crypto_status_t otcrypto_ed25519_keygen_async_finalize(
    crypto_blinded_key_t *private_key, crypto_unblinded_key_t *public_key) {
  // TODO: Ed25519 is not yet implemented.
  return OTCRYPTO_NOT_IMPLEMENTED;
}

crypto_status_t otcrypto_ed25519_sign_async_start(
    const crypto_blinded_key_t *private_key,
    crypto_const_byte_buf_t input_message, eddsa_sign_mode_t sign_mode,
    const ecc_signature_t *signature) {
  // TODO: Ed25519 is not yet implemented.
  return OTCRYPTO_NOT_IMPLEMENTED;
}

crypto_status_t otcrypto_ed25519_sign_async_finalize(
    const ecc_signature_t *signature) {
  // TODO: Ed25519 is not yet implemented.
  return OTCRYPTO_NOT_IMPLEMENTED;
}

crypto_status_t otcrypto_ed25519_verify_async_start(
    const crypto_unblinded_key_t *public_key,
    crypto_const_byte_buf_t input_message, eddsa_sign_mode_t sign_mode,
    const ecc_signature_t *signature) {
  // TODO: Ed25519 is not yet implemented.
  return OTCRYPTO_NOT_IMPLEMENTED;
}

crypto_status_t otcrypto_ed25519_verify_async_finalize(
    hardened_bool_t *verification_result) {
  // TODO: Ed25519 is not yet implemented.
  return OTCRYPTO_NOT_IMPLEMENTED;
}

crypto_status_t otcrypto_x25519_keygen_async_start(
    const crypto_key_config_t *config) {
  // TODO: X25519 is not yet implemented.
  return OTCRYPTO_NOT_IMPLEMENTED;
}

crypto_status_t otcrypto_x25519_keygen_async_finalize(
    crypto_blinded_key_t *private_key, crypto_unblinded_key_t *public_key) {
  // TODO: X25519 is not yet implemented.
  return OTCRYPTO_NOT_IMPLEMENTED;
}

crypto_status_t otcrypto_x25519_async_start(
    const crypto_blinded_key_t *private_key,
    const crypto_unblinded_key_t *public_key) {
  // TODO: X25519 is not yet implemented.
  return OTCRYPTO_NOT_IMPLEMENTED;
}

crypto_status_t otcrypto_x25519_async_finalize(
    crypto_blinded_key_t *shared_secret) {
  // TODO: X25519 is not yet implemented.
  return OTCRYPTO_NOT_IMPLEMENTED;
}
