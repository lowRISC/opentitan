// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/include/ecc_curve25519.h"

#include "sw/device/lib/base/hardened_memory.h"
#include "sw/device/lib/crypto/drivers/entropy.h"
#include "sw/device/lib/crypto/drivers/hmac.h"
#include "sw/device/lib/crypto/impl/ecc/curve25519.h"
#include "sw/device/lib/crypto/impl/integrity.h"
#include "sw/device/lib/crypto/impl/keyblob.h"
#include "sw/device/lib/crypto/impl/status.h"
#include "sw/device/lib/crypto/include/datatypes.h"
#include "sw/device/lib/crypto/include/sha2.h"

// Module ID for status codes.
#define MODULE_ID MAKE_MODULE_ID('e', '2', '5')

/**
 * Check the lengths of public/private keys for curve 25519.
 *
 * This function also does some basic checks on the key struct.
 *
 * Checks the length of caller-allocated buffers for a 25519 unblinded
 * key.
 *
 * @param key Public/private key struct to check.
 * @return OK if the lengths are correct or BAD_ARGS otherwise.
 */
OT_WARN_UNUSED_RESULT
static status_t ed25519_key_check(const otcrypto_unblinded_key_t *key) {
  // Check the key struct and key length.
  if (key == NULL || key->key_length != kCurve25519KeyBytes ||
      key->key == NULL || key->key_mode != kOtcryptoKeyModeEd25519) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(launder32(key->key_length), kCurve25519KeyBytes);

  // Check the integrity of the key.
  if (integrity_unblinded_key_check(key) != kHardenedBoolTrue) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(launder32(integrity_unblinded_key_check(key)),
                    kHardenedBoolTrue);

  return OTCRYPTO_OK;
}

/**
 * Check the length of a signature buffer for EdDSA on Curve25519.
 *
 * This function also does some basic checks on the signature struct.
 *
 * If this check passes on `signature.len`, it is safe to interpret
 * `signature.data` as `curve25519_signature_t *`.
 *
 * @param signature Signature to check.
 * @return OK if the lengths are correct or BAD_ARGS otherwise.
 */
OT_WARN_UNUSED_RESULT
static status_t ed25519_signature_check(otcrypto_word32_buf_t *signature) {
  // Check the signature struct and signature length.
  if (signature == NULL || signature->len > UINT32_MAX / sizeof(uint32_t) ||
      signature->len * sizeof(uint32_t) != sizeof(curve25519_signature_t) ||
      signature->data == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(launder32(signature->len) * sizeof(uint32_t),
                    sizeof(curve25519_signature_t));

  return OTCRYPTO_OK;
}

/**
 * Copy a byte array from src to dst in reverse order.
 *
 * @param dst Destination address.
 * @param src Source address.
 * @param len Array length.
 * @return OK.
 */
static status_t reverse_bytecpy(uint8_t *dst, const uint8_t *src, size_t len) {
  for (size_t i = 0; i < len; i++) {
    dst[i] = src[len - 1 - i];
  }

  return OTCRYPTO_OK;
}

/**
 * Calculate the message prehash.
 *
 * If sign_mode is kOtcryptoEddsaSignModeEddsa, the prehash function is
 * equal to the unity function.
 *
 * If sign_mode is kOtcryptoEddsaSignModeHashEddsa, the prehash function is
 * equal to sha2_512.
 *
 * @param sign_mode The prehash function selection.
 * @param input_message The input message.
 * @param[out] message_ph The message prehash.
 * @return OK.
 */
static status_t ed25519_message_prehash(otcrypto_eddsa_sign_mode_t sign_mode,
                                        otcrypto_const_byte_buf_t input_message,
                                        otcrypto_byte_buf_t *message_ph) {
  // Only a message of length zero can have NULL as data.
  if (input_message.data == NULL && input_message.len != 0) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Instantiate variable for an FI check on the sign mode used.
  otcrypto_eddsa_sign_mode_t sign_mode_used = launder32(0);
  // Use SHA2_512 if the sign mode is kOtcryptoEddsaSignModeHashEddsa.
  if (sign_mode == launder32(kOtcryptoEddsaSignModeHashEddsa)) {
    sign_mode_used =
        launder32(sign_mode_used) | kOtcryptoEddsaSignModeHashEddsa;

    uint32_t input_digest_data[kCurve25519HashWords];
    otcrypto_hash_digest_t input_digest = {
        .data = input_digest_data,
        .len = ARRAYSIZE(input_digest_data),
    };

    HARDENED_TRY(otcrypto_sha2_512(input_message, &input_digest));
    message_ph->data = (uint8_t *)input_digest.data;
    message_ph->len = input_digest.len * sizeof(uint32_t);

    // Use the unity function if the sign mode is kOtcryptoEddsaSignModeEddsa.
  } else if (sign_mode == launder32(kOtcryptoEddsaSignModeEddsa)) {
    sign_mode_used = launder32(sign_mode_used) | kOtcryptoEddsaSignModeEddsa;
    message_ph->data = (uint8_t *)input_message.data;
    message_ph->len = input_message.len;

    // Return OTCRYPTO_BAD_ARGS if the sign mode is none of the above.
  } else {
    return OTCRYPTO_BAD_ARGS;
  }
  // Check if we landed in the correct if branch.
  HARDENED_CHECK_EQ(launder32(sign_mode_used), sign_mode);

  return OTCRYPTO_OK;
}

otcrypto_status_t otcrypto_ed25519_keygen(
    const otcrypto_unblinded_key_t *private_key,
    otcrypto_unblinded_key_t *public_key) {
  // Start the execution of the key generation.
  HARDENED_TRY(otcrypto_ed25519_keygen_async_start(private_key));
  // Finish the keygen operation and get the public key.
  return otcrypto_ed25519_keygen_async_finalize(public_key);
}

otcrypto_status_t otcrypto_ed25519_sign(
    const otcrypto_unblinded_key_t *private_key,
    otcrypto_const_byte_buf_t input_message,
    otcrypto_eddsa_sign_mode_t sign_mode, otcrypto_word32_buf_t *signature) {
  // Instantiate struct to store the secret key digest.
  uint32_t key_digest_data[kCurve25519HashWords];
  otcrypto_hash_digest_t key_digest = {
      .data = key_digest_data,
      .len = ARRAYSIZE(key_digest_data),
  };
  // Instantiate struct to store the message digest.
  uint32_t msg_digest_data[kCurve25519HashWords];
  otcrypto_hash_digest_t msg_digest = {
      .data = msg_digest_data,
      .len = ARRAYSIZE(msg_digest_data),
  };

  // Get the message prehash if needed.
  otcrypto_byte_buf_t message_ph;
  HARDENED_TRY(ed25519_message_prehash(sign_mode, input_message, &message_ph));
  // From this point on we are using input_message_ph as the message.
  otcrypto_const_byte_buf_t input_message_ph = {
      .data = (const uint8_t *const)message_ph.data,
      .len = message_ph.len,
  };

  // Start sign part 1 to calculate the public key and the signature commitment
  // R.
  HARDENED_TRY(otcrypto_ed25519_sign_part1_async_start(
      private_key, input_message_ph, kOtcryptoEddsaSignModeEddsa, &key_digest,
      &msg_digest));
  // Start sign part 2 to calculate the signature response S.
  HARDENED_TRY(otcrypto_ed25519_sign_part2_async_start(
      private_key, input_message_ph, kOtcryptoEddsaSignModeEddsa, signature,
      &key_digest, &msg_digest));
  // Finish the execution and retrieve the signature.
  return otcrypto_ed25519_sign_async_finalize(signature);
}

otcrypto_status_t otcrypto_ed25519_verify(
    const otcrypto_unblinded_key_t *public_key,
    otcrypto_const_byte_buf_t input_message,
    otcrypto_eddsa_sign_mode_t sign_mode, otcrypto_const_word32_buf_t signature,
    hardened_bool_t *verification_result) {
  // Get the message prehash if needed.
  otcrypto_byte_buf_t message_ph;
  HARDENED_TRY(ed25519_message_prehash(sign_mode, input_message, &message_ph));
  // From this point on we are using input_message_ph as the message.
  otcrypto_const_byte_buf_t input_message_ph = {
      .data = (const uint8_t *const)message_ph.data,
      .len = message_ph.len,
  };
  // Start the execution of the verification.
  HARDENED_TRY(otcrypto_ed25519_verify_async_start(
      public_key, input_message_ph, kOtcryptoEddsaSignModeEddsa, signature));
  // Finish the verification operation and get the result.
  return otcrypto_ed25519_verify_async_finalize(verification_result);
}

otcrypto_status_t otcrypto_ed25519_keygen_async_start(
    const otcrypto_unblinded_key_t *private_key) {
  // Check that the entropy complex is initialized.
  HARDENED_TRY(entropy_complex_check());

  // Check the private key.
  HARDENED_TRY(ed25519_key_check(private_key));

  // Instantiate struct to store the secret key digest.
  uint32_t key_digest_data[kCurve25519HashWords];
  otcrypto_hash_digest_t key_digest = {
      .data = key_digest_data,
      .len = ARRAYSIZE(key_digest_data),
  };

  // Compute hash_h_low.
  otcrypto_const_byte_buf_t key_buf = {
      .data = (const uint8_t *const)private_key->key,
      .len = private_key->key_length};
  HARDENED_TRY(otcrypto_sha2_512(key_buf, &key_digest));

  // Start the OTBN keygen app.
  HARDENED_TRY(curve25519_keygen_start(key_digest.data));

  return OTCRYPTO_OK;
}

otcrypto_status_t otcrypto_ed25519_keygen_async_finalize(
    otcrypto_unblinded_key_t *public_key) {
  // Finalize the keygen operation and retrieve the public key.
  HARDENED_TRY(curve25519_keygen_finalize(public_key->key));
  // Calculate the public key checksum.
  public_key->checksum = integrity_unblinded_checksum(public_key);
  return OTCRYPTO_OK;
}

otcrypto_status_t otcrypto_ed25519_sign_part1_async_start(
    const otcrypto_unblinded_key_t *private_key,
    otcrypto_const_byte_buf_t input_message,
    otcrypto_eddsa_sign_mode_t sign_mode, otcrypto_hash_digest_t *key_digest,
    otcrypto_hash_digest_t *msg_digest) {
  // Get the message prehash if needed.
  otcrypto_byte_buf_t message_ph;
  HARDENED_TRY(ed25519_message_prehash(sign_mode, input_message, &message_ph));
  // From this point on we are using input_message_ph as the message.
  otcrypto_const_byte_buf_t input_message_ph = {
      .data = (const uint8_t *const)message_ph.data,
      .len = message_ph.len,
  };

  // Check that the entropy complex is initialized.
  HARDENED_TRY(entropy_complex_check());

  // Check the private key.
  HARDENED_TRY(ed25519_key_check(private_key));

  // Compute hash_h_low.
  // TODO(#28964) Check SCA hardening of the key digest.
  otcrypto_const_byte_buf_t key_buf = {
      .data = (const uint8_t *const)private_key->key,
      .len = private_key->key_length};
  HARDENED_TRY(otcrypto_sha2_512(key_buf, key_digest));

  // Compute SHA-512(prefix || PH(M)).
  size_t msg_byte_len = input_message_ph.len + kCurve25519ScalarBytes;
  uint8_t msg_bytes[msg_byte_len];
  uint32_t *prefix =
      key_digest->data + kCurve25519ScalarBytes / sizeof(uint32_t);
  HARDENED_TRY(hardened_memcpy((uint32_t *)msg_bytes, prefix,
                               kCurve25519ScalarBytes / sizeof(uint32_t)));
  HARDENED_TRY(randomized_bytecopy(&msg_bytes[kCurve25519ScalarBytes],
                                   input_message_ph.data,
                                   input_message_ph.len));

  otcrypto_const_byte_buf_t msg_buf = {.data = msg_bytes, .len = msg_byte_len};
  HARDENED_TRY(otcrypto_sha2_512(msg_buf, msg_digest));

  // Start the OTBN sign stage 1 app.
  HARDENED_TRY(
      curve25519_sign_stage1_start(msg_digest->data, key_digest->data));

  return OTCRYPTO_OK;
}

otcrypto_status_t otcrypto_ed25519_sign_part2_async_start(
    const otcrypto_unblinded_key_t *private_key,
    otcrypto_const_byte_buf_t input_message,
    otcrypto_eddsa_sign_mode_t sign_mode, otcrypto_word32_buf_t *signature,
    otcrypto_hash_digest_t *key_digest, otcrypto_hash_digest_t *msg_digest) {
  // Get the message prehash if needed.
  otcrypto_byte_buf_t message_ph;
  HARDENED_TRY(ed25519_message_prehash(sign_mode, input_message, &message_ph));
  // From this point on we are using input_message_ph as the message.
  otcrypto_const_byte_buf_t input_message_ph = {
      .data = (const uint8_t *const)message_ph.data,
      .len = message_ph.len,
  };

  // Ensure the entropy complex is initialized.
  HARDENED_TRY(entropy_complex_check());

  // Check the signature.
  HARDENED_TRY(ed25519_signature_check(signature));

  // Check the private key.
  HARDENED_TRY(ed25519_key_check(private_key));

  // Finalize the signature stage 1 and retrieve the signature commitment R and
  // public key A.
  curve25519_signature_t sig_curve25519;
  uint32_t public_key_buf[kCurve25519PointWords];
  HARDENED_TRY(
      curve25519_sign_stage1_finalize(&sig_curve25519, public_key_buf));
  reverse_bytecpy((uint8_t *)signature->data, (uint8_t *)sig_curve25519.r,
                  kCurve25519PointBytes);

  otcrypto_unblinded_key_t public_key = {
      .key_mode = kOtcryptoKeyModeEd25519,
      .key_length = kCurve25519PointBytes,
      .key = public_key_buf,
  };
  public_key.checksum = integrity_unblinded_checksum(&public_key);

  // Compute SHA512(R || A || PH(M)).
  size_t challenge_byte_len = input_message_ph.len + 2 * kCurve25519PointBytes;
  uint8_t challenge_bytes[challenge_byte_len];
  memcpy(challenge_bytes, (const uint8_t *)sig_curve25519.r,
         kCurve25519PointBytes);
  memcpy(&challenge_bytes[kCurve25519PointBytes],
         (const uint8_t *)public_key.key, kCurve25519PointBytes);
  memcpy(&challenge_bytes[2 * kCurve25519PointBytes], input_message_ph.data,
         input_message_ph.len);
  otcrypto_const_byte_buf_t challenge_buf = {.data = challenge_bytes,
                                             .len = challenge_byte_len};
  uint32_t challenge_digest_data[kCurve25519HashWords];
  otcrypto_hash_digest_t challenge_digest = {
      .data = challenge_digest_data,
      .len = ARRAYSIZE(challenge_digest_data),
  };
  HARDENED_TRY(otcrypto_sha2_512(challenge_buf, &challenge_digest));

  // Start the OTBN sign stage 2 app.
  HARDENED_TRY(curve25519_sign_stage2_start(
      challenge_digest.data, msg_digest->data, key_digest->data));

  return OTCRYPTO_OK;
}

otcrypto_status_t otcrypto_ed25519_sign_async_finalize(
    otcrypto_word32_buf_t *signature) {
  // Ensure the entropy complex is initialized.
  HARDENED_TRY(entropy_complex_check());

  // Check the signature.
  HARDENED_TRY(ed25519_signature_check(signature));

  // Finalize the signature stage 1 and retrieve the signature response S.
  curve25519_signature_t sig;
  HARDENED_TRY(curve25519_sign_stage2_finalize(&sig));
  memcpy(&(signature->data[kCurve25519PointWords]), sig.s,
         kCurve25519ScalarBytes);

  return OTCRYPTO_OK;
}

otcrypto_status_t otcrypto_ed25519_verify_async_start(
    const otcrypto_unblinded_key_t *public_key,
    otcrypto_const_byte_buf_t input_message,
    otcrypto_eddsa_sign_mode_t sign_mode,
    otcrypto_const_word32_buf_t signature) {
  // Ensure the entropy complex is initialized.
  HARDENED_TRY(entropy_complex_check());

  // Check the public key.
  HARDENED_TRY(ed25519_key_check(public_key));

  // Do some signature struct validity checks.
  HARDENED_TRY(ed25519_signature_check((otcrypto_word32_buf_t *)&signature));
  if (signature.data == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Get the message prehash if needed.
  otcrypto_byte_buf_t message_ph;
  HARDENED_TRY(ed25519_message_prehash(sign_mode, input_message, &message_ph));
  // From this point on we are using input_message_ph as the message.
  otcrypto_const_byte_buf_t input_message_ph = {
      .data = (const uint8_t *const)message_ph.data,
      .len = message_ph.len,
  };

  // Compute SHA512(R || A || PH(M)).
  curve25519_signature_t sig_curve25519;
  reverse_bytecpy((uint8_t *)sig_curve25519.r, (uint8_t *)signature.data,
                  kCurve25519PointBytes);
  memcpy(sig_curve25519.s, &signature.data[kCurve25519PointWords],
         kCurve25519ScalarBytes);
  size_t challenge_byte_len = input_message_ph.len + 2 * kCurve25519PointBytes;
  uint8_t challenge_bytes[challenge_byte_len];
  memcpy(challenge_bytes, (const uint8_t *)sig_curve25519.r,
         kCurve25519PointBytes);
  memcpy(&challenge_bytes[kCurve25519PointBytes],
         (const uint8_t *)public_key->key, kCurve25519PointBytes);
  memcpy(&challenge_bytes[2 * kCurve25519PointBytes], input_message_ph.data,
         input_message_ph.len);
  otcrypto_const_byte_buf_t challenge_buf = {.data = challenge_bytes,
                                             .len = challenge_byte_len};
  uint32_t challenge_digest_data[kCurve25519HashWords];
  otcrypto_hash_digest_t challenge_digest = {
      .data = challenge_digest_data,
      .len = ARRAYSIZE(challenge_digest_data),
  };
  HARDENED_TRY(otcrypto_sha2_512(challenge_buf, &challenge_digest));

  // Start the OTBN verify app.
  HARDENED_TRY(curve25519_verify_start(challenge_digest.data, &sig_curve25519,
                                       public_key->key));

  return OTCRYPTO_OK;
}

otcrypto_status_t otcrypto_ed25519_verify_async_finalize(
    hardened_bool_t *verification_result) {
  // Finalize the verify operation and retrieve the verification result.
  HARDENED_TRY(curve25519_verify_finalize(verification_result));
  return OTCRYPTO_OK;
}
