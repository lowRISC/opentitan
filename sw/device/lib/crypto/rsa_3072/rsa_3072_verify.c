// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/rsa_3072/rsa_3072_verify.h"

#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/dif/dif_hmac.h"
#include "sw/device/lib/runtime/otbn.h"

OTBN_DECLARE_APP_SYMBOLS(run_rsa_verify_3072);  // The OTBN RSA-3072 app.
OTBN_DECLARE_PTR_SYMBOL(run_rsa_verify_3072,
                        mode);  // Mode (constants or modexp).
OTBN_DECLARE_PTR_SYMBOL(run_rsa_verify_3072,
                        out_buf);  // Output buffer (message).
OTBN_DECLARE_PTR_SYMBOL(run_rsa_verify_3072,
                        in_exp);  // The RSA key exponent (n).
OTBN_DECLARE_PTR_SYMBOL(run_rsa_verify_3072, in_mod);  // The RSA modulus (n).
OTBN_DECLARE_PTR_SYMBOL(run_rsa_verify_3072, in_buf);  // The signature (s).
OTBN_DECLARE_PTR_SYMBOL(run_rsa_verify_3072,
                        rr);  // The Montgomery constant R^2.
OTBN_DECLARE_PTR_SYMBOL(run_rsa_verify_3072,
                        m0inv);  // The Montgomery constant m0_inv.

static const otbn_app_t kOtbnAppRsa = OTBN_APP_T_INIT(run_rsa_verify_3072);
static const otbn_ptr_t kOtbnVarRsaMode =
    OTBN_PTR_T_INIT(run_rsa_verify_3072, mode);
static const otbn_ptr_t kOtbnVarRsaOutBuf =
    OTBN_PTR_T_INIT(run_rsa_verify_3072, out_buf);
static const otbn_ptr_t kOtbnVarRsaInExp =
    OTBN_PTR_T_INIT(run_rsa_verify_3072, in_exp);
static const otbn_ptr_t kOtbnVarRsaInMod =
    OTBN_PTR_T_INIT(run_rsa_verify_3072, in_mod);
static const otbn_ptr_t kOtbnVarRsaInBuf =
    OTBN_PTR_T_INIT(run_rsa_verify_3072, in_buf);
static const otbn_ptr_t kOtbnVarRsaRR =
    OTBN_PTR_T_INIT(run_rsa_verify_3072, rr);
static const otbn_ptr_t kOtbnVarRsaM0Inv =
    OTBN_PTR_T_INIT(run_rsa_verify_3072, m0inv);

/* Mode is represented by a single word: 1=constant computation, 2=modexp */
static const uint32_t kOtbnRsaModeNumBytes = sizeof(uint32_t);
static const uint32_t kOtbnRsaModeConstants = 1;
static const uint32_t kOtbnRsaModeModexp = 2;

/* Exponent is represented by a single word */
static const uint32_t kOtbnRsaExponentNumBytes = sizeof(uint32_t);

/**
 * Compute the SHA-256 digest of a message using the HMAC accelerator.
 *
 * This function will block if the HMAC fifo fills up, and wait until it can
 * pass more data.
 *
 * `msg` *must* point to an allocated buffer of at least length `msg_len`.
 *
 * @param hmac HMAC context
 * @param msg Message to hash
 * @param msg_len Length of message in bytes
 * @param[out] digest Resulting digest (little-endian)
 */
dif_result_t sha256(const dif_hmac_t *hmac, const uint8_t *msg, size_t msg_len,
                    dif_hmac_digest_t *digest) {
  // HMAC configuration
  dif_hmac_transaction_t hmac_config = {
      // Note: the "message_endianness" must always be set to little-endian.
      // This setting only affects multi-byte writes. Because msg is a byte
      // array, it will only affect cases where the HMAC driver sees that the
      // message is word-aligned and decides to push multiple bytes at once
      // onto the FIFO by converting the first 4 bytes into a 32-bit integer,
      // which is always little-endian.
      .message_endianness = kDifHmacEndiannessLittle,
      .digest_endianness = kDifHmacEndiannessLittle,
  };

  // Set the HMAC mode to SHA256-only.
  dif_result_t hmac_result = dif_hmac_mode_sha256_start(hmac, hmac_config);
  if (hmac_result != kDifOk) {
    return hmac_result;
  }

  // Pass the message through to the HMAC device.
  size_t bytes_sent = 0;
  while (msg_len > 0) {
    // Push as many bytes as we can onto the FIFO
    hmac_result = dif_hmac_fifo_push(hmac, msg, msg_len, &bytes_sent);
    if ((hmac_result != kDifIpFifoFull) && (hmac_result != kDifOk)) {
      // Unexpected error; return it
      return hmac_result;
    }
    // Advance message pointer
    msg = msg + bytes_sent;
    msg_len = msg_len - bytes_sent;
  }

  // Start processing
  hmac_result = dif_hmac_process(hmac);
  if (hmac_result != kDifOk) {
    return hmac_result;
  }

  // Poll until HMAC is finished processing, and retrieve the digest.
  do {
    hmac_result = dif_hmac_finish(hmac, digest);
  } while (hmac_result == kDifUnavailable);

  // Setting the HMAC configuration to little-endian changes the order of bytes
  // within the words of the digest but not the order of the words themselves;
  // therefore, to make the digest fully little-endian, we need to reverse the
  // words.
  memrev32(digest->digest, ARRAYSIZE(digest->digest));

  return hmac_result;
}

dif_result_t rsa_3072_encode_sha256(const dif_hmac_t *hmac, const uint8_t *msg,
                                    size_t msg_len, rsa_3072_int_t *result) {
  enum { kSha256DigestNumWords = 8 };

  // Message encoding as described in RFC 8017, Section 9.2. The encoded
  // message is:
  //
  // EM = 0x00 || 0x01 || PS || 0x00 || T,
  //
  // where PS is padding made of enough 0xff bytes to meet the desired
  // message length emLen (emLen = 384 bytes for RSA-3072), and T is the DER
  // encoding of the digest. For SHA-256,
  //
  // T = (0x)30 31 30 0d 06 09 60 86 48 01 65 03 04 02 01 05 00 04 20 || H,
  //
  // where H is the 256-bit message digest from SHA-256.
  //
  // Note that the RFC document is using a big-endian representation; here we
  // are using little-endian, so the bytes are reversed.

  // Initially set all bits of the result; we will change the ones that are not
  // part of PS.
  memset(result->data, 0xff, sizeof(result->data));

  // Set 0x00 || 0x01 bytes at most significant end
  result->data[kRsa3072NumWords - 1] = 0x0001ffff;

  // Compute the SHA-256 message digest.
  dif_hmac_digest_t digest;
  dif_result_t sha256_result = sha256(hmac, msg, msg_len, &digest);
  if (sha256_result != kDifOk) {
    return sha256_result;
  }

  // Copy the message digest into the least significant end of the result.
  memcpy(result->data, digest.digest, sizeof(digest.digest));

  // Set remainder of 0x00 || T section
  result->data[kSha256DigestNumWords] = 0x05000420;
  result->data[kSha256DigestNumWords + 1] = 0x03040201;
  result->data[kSha256DigestNumWords + 2] = 0x86480165;
  result->data[kSha256DigestNumWords + 3] = 0x0d060960;
  result->data[kSha256DigestNumWords + 4] = 0x00303130;

  return kDifOk;
}

/**
 * Copies a 3072-bit number from the CPU memory to OTBN data memory.
 *
 * @param otbn The OTBN context object.
 * @param src Source of the data to copy.
 * @param dst Pointer to the destination in OTBN's data memory.
 * @return The result of the operation.
 */
otbn_result_t write_rsa_3072_int_to_otbn(otbn_t *otbn,
                                         const rsa_3072_int_t *src,
                                         otbn_ptr_t dst) {
  return otbn_copy_data_to_otbn(otbn, kRsa3072NumBytes, src->data, dst);
}

/**
 * Copies a 3072-bit number from OTBN data memory to CPU memory.
 *
 * @param otbn The OTBN context object.
 * @param src The pointer in OTBN data memory to copy from.
 * @param dst The destination of the copied data in main memory (preallocated).
 * @return The result of the operation.
 */
otbn_result_t read_rsa_3072_int_from_otbn(otbn_t *otbn, const otbn_ptr_t src,
                                          rsa_3072_int_t *dst) {
  return otbn_copy_data_from_otbn(otbn, kRsa3072NumBytes, src, dst->data);
}

// TODO: This implementation waits while OTBN is processing; it should be
// modified to be non-blocking.
otbn_result_t rsa_3072_compute_constants(
    otbn_t *otbn, const rsa_3072_public_key_t *public_key,
    rsa_3072_constants_t *result) {
  // Load the RSA app.
  OTBN_RETURN_IF_ERROR(otbn_load_app(otbn, kOtbnAppRsa));

  // Set mode to compute constants.
  OTBN_RETURN_IF_ERROR(otbn_copy_data_to_otbn(
      otbn, kOtbnRsaModeNumBytes, &kOtbnRsaModeConstants, kOtbnVarRsaMode));

  // Set the modulus (n).
  OTBN_RETURN_IF_ERROR(
      write_rsa_3072_int_to_otbn(otbn, &public_key->n, kOtbnVarRsaInMod));

  // Start the OTBN routine.
  OTBN_RETURN_IF_ERROR(otbn_execute(otbn));

  // Spin here waiting for OTBN to complete.
  OTBN_RETURN_IF_ERROR(otbn_busy_wait_for_done(otbn));

  // Read constant rr out of DMEM.
  OTBN_RETURN_IF_ERROR(
      read_rsa_3072_int_from_otbn(otbn, kOtbnVarRsaRR, &result->rr));

  // Read constant m0_inv out of DMEM.
  OTBN_RETURN_IF_ERROR(otbn_copy_data_from_otbn(
      otbn, kOtbnWlenBytes, kOtbnVarRsaM0Inv, result->m0_inv));

  return kOtbnOk;
}

// TODO: This implementation waits while OTBN is processing; it should be
// modified to be non-blocking.
otbn_result_t rsa_3072_verify(otbn_t *otbn, const rsa_3072_int_t *signature,
                              const rsa_3072_int_t *message,
                              const rsa_3072_public_key_t *public_key,
                              const rsa_3072_constants_t *constants,
                              hardened_bool_t *result) {
  // For now, only the F4 modulus is supported.
  if (public_key->e != 65537) {
    return kOtbnBadArg;
  }

  // TODO: Check that s < n, reject signature otherwise

  // Load the RSA app.
  OTBN_RETURN_IF_ERROR(otbn_load_app(otbn, kOtbnAppRsa));

  // Set mode to perform modular exponentiation.
  OTBN_RETURN_IF_ERROR(otbn_copy_data_to_otbn(
      otbn, kOtbnRsaModeNumBytes, &kOtbnRsaModeModexp, kOtbnVarRsaMode));

  // Set the exponent (e).
  OTBN_RETURN_IF_ERROR(otbn_copy_data_to_otbn(
      otbn, kOtbnRsaExponentNumBytes, &public_key->e, kOtbnVarRsaInExp));

  // Set the modulus (n).
  OTBN_RETURN_IF_ERROR(
      write_rsa_3072_int_to_otbn(otbn, &public_key->n, kOtbnVarRsaInMod));

  // Set the signature.
  OTBN_RETURN_IF_ERROR(
      write_rsa_3072_int_to_otbn(otbn, signature, kOtbnVarRsaInBuf));

  // Set the precomputed constant R^2.
  OTBN_RETURN_IF_ERROR(
      write_rsa_3072_int_to_otbn(otbn, &constants->rr, kOtbnVarRsaRR));

  // Set the precomputed constant m0_inv.
  OTBN_RETURN_IF_ERROR(otbn_copy_data_to_otbn(
      otbn, kOtbnWlenBytes, constants->m0_inv, kOtbnVarRsaM0Inv));

  // Start the OTBN routine.
  OTBN_RETURN_IF_ERROR(otbn_execute(otbn));

  // Spin here waiting for OTBN to complete.
  OTBN_RETURN_IF_ERROR(otbn_busy_wait_for_done(otbn));

  // Read recovered message out of OTBN dmem.
  rsa_3072_int_t recoveredMessage;
  OTBN_RETURN_IF_ERROR(
      read_rsa_3072_int_from_otbn(otbn, kOtbnVarRsaOutBuf, &recoveredMessage));

  // TODO: harden this memory comparison
  // Check if recovered message matches expectation
  *result = kHardenedBoolTrue;
  for (int i = 0; i < kRsa3072NumWords; i++) {
    if (recoveredMessage.data[i] != message->data[i]) {
      *result = kHardenedBoolFalse;
    }
  }

  return kOtbnOk;
}
