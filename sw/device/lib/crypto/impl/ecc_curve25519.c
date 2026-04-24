// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/include/ecc_curve25519.h"

#include "sw/device/lib/base/hardened_memory.h"
#include "sw/device/lib/crypto/drivers/hmac.h"
#include "sw/device/lib/crypto/impl/ecc/curve25519.h"
#include "sw/device/lib/crypto/impl/keyblob.h"
#include "sw/device/lib/crypto/impl/status.h"
#include "sw/device/lib/crypto/include/config.h"
#include "sw/device/lib/crypto/include/datatypes.h"
#include "sw/device/lib/crypto/include/drbg.h"
#include "sw/device/lib/crypto/include/integrity.h"
#include "sw/device/lib/crypto/include/sha2.h"

// Module ID for status codes.
#define MODULE_ID MAKE_MODULE_ID('e', '2', '5')

// RFC 8032 dom2(1, "") prefix for Ed25519ph (HashEdDSA)
static const uint8_t kDom2Prefix[34] = {
    'S', 'i', 'g', 'E', 'd', '2', '5', '5', '1', '9', ' ', 'n',
    'o', ' ', 'E', 'd', '2', '5', '5', '1', '9', ' ', 'c', 'o',
    'l', 'l', 'i', 's', 'i', 'o', 'n', 's', 1,   0  // F=1 (Ed25519ph), C_len=0
};

/**
 * Check the lengths of private keys for curve 25519.
 *
 * Checks the length of caller-allocated buffers for a 25519 private key.
 *
 * @param private_key Private key struct to check.
 * @return OK if the lengths are correct or BAD_ARGS otherwise.
 */
OT_WARN_UNUSED_RESULT
static status_t ed25519_private_key_length_check(
    const otcrypto_blinded_key_t *private_key) {
  if (private_key == NULL || private_key->keyblob == NULL) {
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
  if (private_key->config.key_length != kCurve25519KeyBytes) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(launder32(private_key->config.key_length),
                    kCurve25519KeyBytes);

  // Check the key mode.
  if (private_key->config.key_mode != kOtcryptoKeyModeEd25519) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(launder32(private_key->config.key_mode),
                    kOtcryptoKeyModeEd25519);

  // Check the integrity of the key.
  if (integrity_blinded_key_check(private_key) != kHardenedBoolTrue) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(launder32(integrity_blinded_key_check(private_key)),
                    kHardenedBoolTrue);

  return OTCRYPTO_OK;
}

/**
 * Check the lengths of public keys for curve 25519.
 *
 * This function also does some basic checks on the key struct.
 *
 * Checks the length of caller-allocated buffers for a 25519 unblinded
 * key.
 *
 * @param key Public key struct to check.
 * @return OK if the lengths are correct or BAD_ARGS otherwise.
 */
OT_WARN_UNUSED_RESULT
static status_t ed25519_public_key_length_check(
    const otcrypto_unblinded_key_t *key) {
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

  // Verify the input buffer
  HARDENED_CHECK_EQ(kHardenedBoolTrue, OTCRYPTO_CHECK_BUF(signature));

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
 * @param prehash_buffer Prehash buffer.
 * @return OK.
 */
static status_t ed25519_message_prehash(
    otcrypto_eddsa_sign_mode_t sign_mode,
    const otcrypto_const_byte_buf_t *input_message,
    otcrypto_byte_buf_t *message_ph, uint32_t *prehash_buffer) {
  // Only a message of length zero can have NULL as data.
  if (input_message->data == NULL && input_message->len != 0) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Instantiate variable for an FI check on the sign mode used.
  otcrypto_eddsa_sign_mode_t sign_mode_used = launder32(0);
  // Use SHA2_512 if the sign mode is kOtcryptoEddsaSignModeHashEddsa.
  if (sign_mode == launder32(kOtcryptoEddsaSignModeHashEddsa)) {
    sign_mode_used =
        launder32(sign_mode_used) | kOtcryptoEddsaSignModeHashEddsa;

    otcrypto_hash_digest_t input_digest = {
        .data = prehash_buffer,
        .len = kCurve25519HashWords,
    };

    HARDENED_TRY(otcrypto_sha2_512(input_message, &input_digest));
    *message_ph =
        OTCRYPTO_MAKE_BUF(otcrypto_byte_buf_t, (uint8_t *)input_digest.data,
                          input_digest.len * sizeof(uint32_t));
    message_ph->data = (uint8_t *)input_digest.data;
    message_ph->len = input_digest.len * sizeof(uint32_t);

    // Use the unity function if the sign mode is kOtcryptoEddsaSignModeEddsa.
  } else if (sign_mode == launder32(kOtcryptoEddsaSignModeEddsa)) {
    sign_mode_used = launder32(sign_mode_used) | kOtcryptoEddsaSignModeEddsa;
    *message_ph =
        OTCRYPTO_MAKE_BUF(otcrypto_byte_buf_t, (uint8_t *)input_message->data,
                          input_message->len);
    message_ph->data = (uint8_t *)input_message->data;
    message_ph->len = input_message->len;

    // Return OTCRYPTO_BAD_ARGS if the sign mode is none of the above.
  } else {
    return OTCRYPTO_BAD_ARGS;
  }
  // Check if we landed in the correct if branch.
  HARDENED_CHECK_EQ(launder32(sign_mode_used), sign_mode);

  // Verify the output buffer
  HARDENED_CHECK_EQ(kHardenedBoolTrue, OTCRYPTO_CHECK_BUF(message_ph));

  return OTCRYPTO_OK;
}

/**
 * Clamp the lower half of the h digest, to create the scalar s.
 *
 * This function is in accordance with RFC 8032, see Section 5.1.5 Step 2.
 *
 * @param h_hash_low The lower 256 bits of the h digest.
 * @param[out] s, the clamped scalar s.
 * @return OK.
 */
OT_WARN_UNUSED_RESULT
static status_t ed25519_clamp(uint32_t hash_h_low[kCurve25519HalfHashWords]) {
  // Set the lower 3 bits and the MSB to 0, set the MSB-1 to 1.
  hash_h_low[0] &= 0xfffffff8;
  hash_h_low[kCurve25519HalfHashWords - 1] &= 0x7fffffff;
  hash_h_low[kCurve25519HalfHashWords - 1] |= 0x40000000;
  return OTCRYPTO_OK;
}

/**
 * Create an arithmetic sharing of a scalar x such that x0 - x1 = x and
 * x0 > x1.
 *
 * Given a scalar of size at most 32 * `scalar_len` bits and a `share_len`
 * with `share_len >= scalar_len`, this function first randonmly chooses a
 * random share x1 of size (32 * `share_len`) - 1 bits, then computes
 * x0 = x + x1. Since the MSB of x1 is unset, we are sure that x0 is of at most
 * 32 * `scalar_len` bits.
 *
 * Importantly, the MSB of x0 is the carry bit of the addition x + x1 which, if
 * observed, leaks the information about the size of x. To alleviate this,
 * `share_len` should be significantly larger than `scalar_len` which reduces
 * the probability that the carry bit is set.
 *
 * @param scalar The scalar to be arithmetically masked.
 * @param scalar_len The size of the scalar in number of 32-bit words.
 * @param[out] share0 The first share of the arithmetic sharing.
 * @param[out] share1 The second share of the arithmetic sharing.
 * @param share_len The size of of the shared scalars in number of 32-bit words.
 * @return OK.
 */
OT_WARN_UNUSED_RESULT
static status_t ed25519_mask_scalar(uint32_t *scalar, size_t scalar_len,
                                    uint32_t *share0, uint32_t *share1,
                                    size_t share_len) {
  // Copy the unmasked share into a larger buffer and set the
  // `share_len - scalar_len` upper words to 0. Since the scalars in Ed25519
  // can be of different sizes, we resort here to a VLA.
  uint32_t buf[share_len];
  memset(buf, 0, share_len << 2);
  hardened_memshred(buf, scalar_len);
  HARDENED_TRY(hardened_memcpy(buf, scalar, scalar_len));

  // Set share1 to a random value and unset its MSB.
  otcrypto_word32_buf_t share1_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, share1, share_len);
  otcrypto_const_byte_buf_t kEmptyBuffer =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, NULL, 0);
  hardened_memshred(share1, share_len);
  share1[share_len - 1] &= 0x7fffffff;

  // Compute share0 = share + share1.
  HARDENED_TRY(hardened_add(buf, share1, share_len, share0));

  return OTCRYPTO_OK;
}

/**
 * Unmasks the private key, computes the SHA-512 digest, clamps the lower half,
 * and returns the arithmetically masked scalar 's'.
 *
 * The full key digest is also returned because the upper half is needed as a
 * prefix during the first stage of signature generation.
 *
 * @param private_key The blinded private key.
 * @param[out] key_digest The 512-bit SHA-512 hash of the unmasked key.
 * @param[out] masked_s The clamped and masked scalar 's'.
 * @return OK or error status.
 */
OT_WARN_UNUSED_RESULT
static otcrypto_status_t ed25519_compute_scalar_and_prefix(
    const otcrypto_blinded_key_t *private_key,
    otcrypto_hash_digest_t *key_digest,
    curve25519_masked_scalar_s_t *masked_s) {
  // Compute hash_h.
  if (private_key->config.hw_backed == kHardenedBoolFalse) {
    uint32_t seed_data[kCurve25519KeyBytes / sizeof(uint32_t)];
    uint32_t *share0 = private_key->keyblob;
    uint32_t *share1 =
        private_key->keyblob + keyblob_share_num_words(private_key->config);

    // Unmask the seed using addition modulo 2^256.
    HARDENED_TRY(hardened_add(share0, share1, ARRAYSIZE(seed_data), seed_data));

    otcrypto_const_byte_buf_t key_buf =
        OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t,
                          (const uint8_t *const)seed_data, kCurve25519KeyBytes);
    HARDENED_TRY(otcrypto_sha2_512(&key_buf, key_digest));

    // Memshred the unmasked seed.
    HARDENED_TRY(hardened_memshred(seed_data, ARRAYSIZE(seed_data)));
  } else {
    // Hardware-backed keys are not supported at the moment.
    return OTCRYPTO_NOT_IMPLEMENTED;
  }

  // Immediately clamp the lower half of hash_h to create the secret scalar s.
  HARDENED_TRY(ed25519_clamp(key_digest->data));

  // Arithmetically mask s before passing it to the OTBN app.
  HARDENED_TRY(ed25519_mask_scalar(key_digest->data, kCurve25519ScalarWords,
                                   masked_s->share0, masked_s->share1,
                                   kCurve25519MaskedScalarSWords));

  return OTCRYPTO_OK;
}

otcrypto_status_t otcrypto_ed25519_public_key_from_private(
    const otcrypto_blinded_key_t *private_key,
    otcrypto_unblinded_key_t *public_key) {
  if (public_key == NULL || public_key->key == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }
  // Start the execution of the key generation.
  HARDENED_TRY(
      otcrypto_ed25519_public_key_from_private_async_start(private_key));
  // Finish the keygen operation and get the public key.
  return otcrypto_ed25519_public_key_from_private_async_finalize(public_key);
}

otcrypto_status_t otcrypto_ed25519_sign(
    const otcrypto_blinded_key_t *private_key,
    const otcrypto_const_byte_buf_t *input_message,
    otcrypto_eddsa_sign_mode_t sign_mode, otcrypto_word32_buf_t *signature) {
  // Validate signature buffer
  HARDENED_TRY(ed25519_signature_check(signature));

  // Allocate the buffers for the shared r scalar.
  uint32_t r0_data[kCurve25519MaskedScalarRWords];
  uint32_t r1_data[kCurve25519MaskedScalarRWords];
  otcrypto_word32_buf_t r0 = OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, r0_data,
                                               kCurve25519MaskedScalarRWords);
  otcrypto_word32_buf_t r1 = OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, r1_data,
                                               kCurve25519MaskedScalarRWords);

  // Allocate the buffers for the shared s scalar.
  uint32_t s0_data[kCurve25519MaskedScalarSWords];
  uint32_t s1_data[kCurve25519MaskedScalarSWords];
  otcrypto_word32_buf_t s0 = OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, s0_data,
                                               kCurve25519MaskedScalarSWords);
  otcrypto_word32_buf_t s1 = OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, s1_data,
                                               kCurve25519MaskedScalarSWords);

  uint32_t prehash_buffer[kCurve25519HashWords];
  otcrypto_byte_buf_t message_ph;
  HARDENED_TRY(ed25519_message_prehash(sign_mode, input_message, &message_ph,
                                       prehash_buffer));

  // From this point on we are using input_message_ph as the message.
  otcrypto_const_byte_buf_t input_message_ph =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t,
                        (const uint8_t *const)message_ph.data, message_ph.len);

  // Start sign part 1 to calculate the public key and the signature commitment
  // R.
  HARDENED_TRY(otcrypto_ed25519_sign_part1_async_start(
      private_key, &input_message_ph, sign_mode, &s0, &s1, &r0, &r1));
  // Start sign part 2 to calculate the signature response S.
  HARDENED_TRY(otcrypto_ed25519_sign_part2_async_start(
      private_key, &input_message_ph, sign_mode, signature, &s0, &s1, &r0,
      &r1));
  // Finish the execution and retrieve the signature.
  return otcrypto_ed25519_sign_async_finalize(signature);
}

otcrypto_status_t otcrypto_ed25519_verify(
    const otcrypto_unblinded_key_t *public_key,
    const otcrypto_const_byte_buf_t *input_message,
    otcrypto_eddsa_sign_mode_t sign_mode,
    const otcrypto_const_word32_buf_t *signature,
    hardened_bool_t *verification_result) {
  if (verification_result == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  uint32_t prehash_buffer[kCurve25519HashWords];
  otcrypto_byte_buf_t message_ph;
  HARDENED_TRY(ed25519_message_prehash(sign_mode, input_message, &message_ph,
                                       prehash_buffer));

  otcrypto_const_byte_buf_t input_message_ph =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t,
                        (const uint8_t *const)message_ph.data, message_ph.len);
  // Start the execution of the verification.
  HARDENED_TRY(otcrypto_ed25519_verify_async_start(
      public_key, &input_message_ph, sign_mode, signature));
  // Finish the verification operation and get the result.
  return otcrypto_ed25519_verify_async_finalize(verification_result);
}

otcrypto_status_t otcrypto_ed25519_sign_verify(
    const otcrypto_blinded_key_t *private_key,
    const otcrypto_unblinded_key_t *public_key,
    const otcrypto_const_byte_buf_t *input_message,
    otcrypto_eddsa_sign_mode_t sign_mode, otcrypto_word32_buf_t *signature) {
  // Signature generation.
  HARDENED_TRY(
      otcrypto_ed25519_sign(private_key, input_message, sign_mode, signature));

  // Verify signature before releasing it.
  otcrypto_const_word32_buf_t signature_check = OTCRYPTO_MAKE_BUF(
      otcrypto_const_word32_buf_t, signature->data, signature->len);
  hardened_bool_t verification_result = kHardenedBoolFalse;
  HARDENED_TRY(otcrypto_ed25519_verify(public_key, input_message, sign_mode,
                                       &signature_check, &verification_result));

  // Trap if signature verification failed.
  HARDENED_CHECK_EQ(verification_result, kHardenedBoolTrue);
  return OTCRYPTO_OK;
}

otcrypto_status_t otcrypto_ed25519_public_key_from_private_async_start(
    const otcrypto_blinded_key_t *private_key) {
  // Check the private key.
  HARDENED_TRY(ed25519_private_key_length_check(private_key));

  // Instantiate struct to store the secret key digest.
  uint32_t key_digest_data[kCurve25519HashWords];
  otcrypto_hash_digest_t key_digest = {
      .data = key_digest_data,
      .len = ARRAYSIZE(key_digest_data),
  };

  curve25519_masked_scalar_s_t s;

  // Compute the digest and scalar
  HARDENED_TRY(ed25519_compute_scalar_and_prefix(private_key, &key_digest, &s));

  // Start the OTBN keygen app.
  HARDENED_TRY(curve25519_keygen_start(&s));

  return otcrypto_eval_exit(OTCRYPTO_OK);
}

otcrypto_status_t otcrypto_ed25519_public_key_from_private_async_finalize(
    otcrypto_unblinded_key_t *public_key) {
  // Finalize the keygen operation and retrieve the public key.
  HARDENED_TRY_WIPE_DMEM(curve25519_keygen_finalize(public_key->key));
  // Calculate the public key checksum.
  public_key->checksum = integrity_unblinded_checksum(public_key);
  return otcrypto_eval_exit(OTCRYPTO_OK);
}

otcrypto_status_t otcrypto_ed25519_sign_part1_async_start(
    const otcrypto_blinded_key_t *private_key,
    const otcrypto_const_byte_buf_t *input_message_ph,
    otcrypto_eddsa_sign_mode_t sign_mode, otcrypto_word32_buf_t *s0,
    otcrypto_word32_buf_t *s1, otcrypto_word32_buf_t *r0,
    otcrypto_word32_buf_t *r1) {
  // Check the private key.
  HARDENED_TRY(ed25519_private_key_length_check(private_key));

  // Instantiate struct to store the secret key digest.
  uint32_t key_digest_data[kCurve25519HashWords];
  otcrypto_hash_digest_t key_digest = {
      .data = key_digest_data,
      .len = ARRAYSIZE(key_digest_data),
  };
  curve25519_masked_scalar_s_t s;

  // Compute the digest and scalar
  HARDENED_TRY(ed25519_compute_scalar_and_prefix(private_key, &key_digest, &s));

  HARDENED_TRY(
      hardened_memcpy(s0->data, s.share0, kCurve25519MaskedScalarSWords));
  HARDENED_TRY(
      hardened_memcpy(s1->data, s.share1, kCurve25519MaskedScalarSWords));

  // Prepend the dom2 prefix
  size_t dom2_len =
      (sign_mode == kOtcryptoEddsaSignModeHashEddsa) ? sizeof(kDom2Prefix) : 0;
  size_t msg_byte_len =
      dom2_len + kCurve25519ScalarBytes + input_message_ph->len;
  uint8_t msg_bytes[msg_byte_len];
  size_t offset = 0;

  if (dom2_len > 0) {
    memcpy(msg_bytes, kDom2Prefix, dom2_len);
    offset += dom2_len;
  }

  // Compute SHA-512(prefix || PH(M)).
  uint32_t *prefix =
      key_digest.data + kCurve25519ScalarBytes / sizeof(uint32_t);
  memcpy(&msg_bytes[offset], prefix, kCurve25519ScalarBytes);
  offset += kCurve25519ScalarBytes;
  memcpy(&msg_bytes[offset], input_message_ph->data, input_message_ph->len);

  // Instantiate struct to store the message digest.
  uint32_t msg_digest_data[kCurve25519HashWords];
  otcrypto_hash_digest_t msg_digest = {
      .data = msg_digest_data,
      .len = ARRAYSIZE(msg_digest_data),
  };

  otcrypto_const_byte_buf_t msg_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, msg_bytes, msg_byte_len);
  HARDENED_TRY(otcrypto_sha2_512(&msg_buf, &msg_digest));

  // Arithmetically mask r before passing it to the OTBN app.
  HARDENED_TRY(ed25519_mask_scalar(msg_digest.data, kCurve25519HashWords,
                                   r0->data, r1->data,
                                   kCurve25519MaskedScalarRWords));

  curve25519_masked_scalar_r_t r;
  HARDENED_TRY(
      hardened_memcpy(r.share0, r0->data, kCurve25519MaskedScalarRWords));
  HARDENED_TRY(
      hardened_memcpy(r.share1, r1->data, kCurve25519MaskedScalarRWords));

  // Start the OTBN sign stage 1 app.
  HARDENED_TRY(curve25519_sign_stage1_start(&r, &s));

  return otcrypto_eval_exit(OTCRYPTO_OK);
}

otcrypto_status_t otcrypto_ed25519_sign_part2_async_start(
    const otcrypto_blinded_key_t *private_key,
    const otcrypto_const_byte_buf_t *input_message_ph,
    otcrypto_eddsa_sign_mode_t sign_mode, otcrypto_word32_buf_t *signature,
    otcrypto_word32_buf_t *s0, otcrypto_word32_buf_t *s1,
    otcrypto_word32_buf_t *r0, otcrypto_word32_buf_t *r1) {
  // Check the signature.
  HARDENED_TRY(ed25519_signature_check(signature));

  // Check the private key.
  HARDENED_TRY(ed25519_private_key_length_check(private_key));

  // Finalize the signature stage 1 and retrieve the signature commitment R and
  // public key A.
  curve25519_signature_t sig_curve25519;
  uint32_t public_key_buf[kCurve25519PointWords];
  HARDENED_TRY_WIPE_DMEM(
      curve25519_sign_stage1_finalize(&sig_curve25519, public_key_buf));
  reverse_bytecpy((uint8_t *)signature->data, (uint8_t *)sig_curve25519.r,
                  kCurve25519PointBytes);

  // Prepend the dom2 prefix
  size_t dom2_len =
      (sign_mode == kOtcryptoEddsaSignModeHashEddsa) ? sizeof(kDom2Prefix) : 0;
  size_t challenge_byte_len =
      dom2_len + input_message_ph->len + 2 * kCurve25519PointBytes;
  uint8_t challenge_bytes[challenge_byte_len];

  memcpy(challenge_bytes, kDom2Prefix, dom2_len);
  size_t offset = dom2_len;

  memcpy(&challenge_bytes[offset], (const uint8_t *)sig_curve25519.r,
         kCurve25519PointBytes);
  offset += kCurve25519PointBytes;
  memcpy(&challenge_bytes[offset], (const uint8_t *)public_key_buf,
         kCurve25519PointBytes);
  offset += kCurve25519PointBytes;
  memcpy(&challenge_bytes[offset], input_message_ph->data,
         input_message_ph->len);

  otcrypto_const_byte_buf_t challenge_buf = OTCRYPTO_MAKE_BUF(
      otcrypto_const_byte_buf_t, challenge_bytes, challenge_byte_len);
  uint32_t challenge_digest_data[kCurve25519HashWords];
  otcrypto_hash_digest_t challenge_digest = {
      .data = challenge_digest_data,
      .len = ARRAYSIZE(challenge_digest_data),
  };
  HARDENED_TRY(otcrypto_sha2_512(&challenge_buf, &challenge_digest));

  curve25519_masked_scalar_s_t s;
  HARDENED_TRY(
      hardened_memcpy(s.share0, s0->data, kCurve25519MaskedScalarSWords));
  HARDENED_TRY(
      hardened_memcpy(s.share1, s1->data, kCurve25519MaskedScalarSWords));

  curve25519_masked_scalar_r_t r;
  HARDENED_TRY(
      hardened_memcpy(r.share0, r0->data, kCurve25519MaskedScalarRWords));
  HARDENED_TRY(
      hardened_memcpy(r.share1, r1->data, kCurve25519MaskedScalarRWords));

  // Start the OTBN sign stage 2 app.
  HARDENED_TRY(curve25519_sign_stage2_start(challenge_digest.data, &r, &s));

  return otcrypto_eval_exit(OTCRYPTO_OK);
}

otcrypto_status_t otcrypto_ed25519_sign_async_finalize(
    otcrypto_word32_buf_t *signature) {
  // Check the signature.
  HARDENED_TRY(ed25519_signature_check(signature));

  // Finalize the signature stage 1 and retrieve the signature response S.
  curve25519_signature_t sig;
  HARDENED_TRY_WIPE_DMEM(curve25519_sign_stage2_finalize(&sig));
  memcpy(&(signature->data[kCurve25519PointWords]), sig.s,
         kCurve25519ScalarBytes);

  return otcrypto_eval_exit(OTCRYPTO_OK);
}

otcrypto_status_t otcrypto_ed25519_verify_async_start(
    const otcrypto_unblinded_key_t *public_key,
    const otcrypto_const_byte_buf_t *input_message_ph,
    otcrypto_eddsa_sign_mode_t sign_mode,
    const otcrypto_const_word32_buf_t *signature) {
  // Check the public key.
  HARDENED_TRY(ed25519_public_key_length_check(public_key));

  // Do some signature struct validity checks.
  HARDENED_TRY(ed25519_signature_check((otcrypto_word32_buf_t *)signature));
  if (signature->data == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Compute SHA512(R || A || PH(M)).
  curve25519_signature_t sig_curve25519;
  reverse_bytecpy((uint8_t *)sig_curve25519.r, (uint8_t *)signature->data,
                  kCurve25519PointBytes);
  memcpy(sig_curve25519.s, &signature->data[kCurve25519PointWords],
         kCurve25519ScalarBytes);

  // Prepend the dom2 prefix
  size_t dom2_len =
      (sign_mode == kOtcryptoEddsaSignModeHashEddsa) ? sizeof(kDom2Prefix) : 0;
  size_t challenge_byte_len =
      dom2_len + input_message_ph->len + 2 * kCurve25519PointBytes;
  uint8_t challenge_bytes[challenge_byte_len];

  memcpy(challenge_bytes, kDom2Prefix, dom2_len);
  size_t offset = dom2_len;

  memcpy(&challenge_bytes[offset], (const uint8_t *)sig_curve25519.r,
         kCurve25519PointBytes);
  offset += kCurve25519PointBytes;
  memcpy(&challenge_bytes[offset], (const uint8_t *)public_key->key,
         kCurve25519PointBytes);
  offset += kCurve25519PointBytes;
  memcpy(&challenge_bytes[offset], input_message_ph->data,
         input_message_ph->len);

  otcrypto_const_byte_buf_t challenge_buf = OTCRYPTO_MAKE_BUF(
      otcrypto_const_byte_buf_t, challenge_bytes, challenge_byte_len);
  uint32_t challenge_digest_data[kCurve25519HashWords];
  otcrypto_hash_digest_t challenge_digest = {
      .data = challenge_digest_data,
      .len = ARRAYSIZE(challenge_digest_data),
  };
  HARDENED_TRY(otcrypto_sha2_512(&challenge_buf, &challenge_digest));

  // Start the OTBN verify app.
  HARDENED_TRY_WIPE_DMEM(curve25519_verify_start(
      challenge_digest.data, &sig_curve25519, public_key->key));

  return otcrypto_eval_exit(OTCRYPTO_OK);
}

otcrypto_status_t otcrypto_ed25519_verify_async_finalize(
    hardened_bool_t *verification_result) {
  // Finalize the verify operation and retrieve the verification result.
  HARDENED_TRY_WIPE_DMEM(curve25519_verify_finalize(verification_result));
  return otcrypto_eval_exit(OTCRYPTO_OK);
}
