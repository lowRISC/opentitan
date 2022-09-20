// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/impl/rsa_3072/rsa_3072_verify.h"

#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/crypto/drivers/hmac.h"
#include "sw/device/lib/crypto/drivers/otbn.h"
#include "sw/device/lib/crypto/impl/otbn_util.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

OTBN_DECLARE_APP_SYMBOLS(run_rsa_verify_3072);  // The OTBN RSA-3072 app.
OTBN_DECLARE_SYMBOL_ADDR(run_rsa_verify_3072,
                         mode);  // Mode (constants or modexp).
OTBN_DECLARE_SYMBOL_ADDR(run_rsa_verify_3072,
                         out_buf);  // Output buffer (message).
OTBN_DECLARE_SYMBOL_ADDR(run_rsa_verify_3072, in_mod);  // The RSA modulus (n).
OTBN_DECLARE_SYMBOL_ADDR(run_rsa_verify_3072, in_buf);  // The signature (s).
OTBN_DECLARE_SYMBOL_ADDR(run_rsa_verify_3072,
                         rr);  // The Montgomery constant R^2.
OTBN_DECLARE_SYMBOL_ADDR(run_rsa_verify_3072,
                         m0inv);  // The Montgomery constant m0_inv.

static const otbn_app_t kOtbnAppRsa = OTBN_APP_T_INIT(run_rsa_verify_3072);
static const otbn_addr_t kOtbnVarRsaMode =
    OTBN_ADDR_T_INIT(run_rsa_verify_3072, mode);
static const otbn_addr_t kOtbnVarRsaOutBuf =
    OTBN_ADDR_T_INIT(run_rsa_verify_3072, out_buf);
static const otbn_addr_t kOtbnVarRsaInMod =
    OTBN_ADDR_T_INIT(run_rsa_verify_3072, in_mod);
static const otbn_addr_t kOtbnVarRsaInBuf =
    OTBN_ADDR_T_INIT(run_rsa_verify_3072, in_buf);
static const otbn_addr_t kOtbnVarRsaRR =
    OTBN_ADDR_T_INIT(run_rsa_verify_3072, rr);
static const otbn_addr_t kOtbnVarRsaM0Inv =
    OTBN_ADDR_T_INIT(run_rsa_verify_3072, m0inv);

/* Mode is represented by a single word: 1=constant computation, 2=modexp */
static const uint32_t kOtbnRsaModeNumWords = 1;
static const uint32_t kOtbnRsaModeConstants = 1;
static const uint32_t kOtbnRsaModeModexp = 2;

// TODO: Change the error type here to a crypto_error_t once that type exists.
hmac_error_t rsa_3072_encode_sha256(const uint8_t *msg, size_t msgLen,
                                    rsa_3072_int_t *result) {
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
  hmac_sha256_init();
  hmac_error_t err;
  if (msg != NULL) {
    err = hmac_sha256_update(msg, msgLen);
    if (err != kHmacOk) {
      return err;
    }
  }
  hmac_digest_t digest;
  err = hmac_sha256_final(&digest);
  if (err != kHmacOk) {
    return err;
  }

  // Copy the message digest into the least significant end of the result.
  memcpy(result->data, digest.digest, sizeof(digest.digest));

  // Set remainder of 0x00 || T section
  result->data[kSha256DigestNumWords] = 0x05000420;
  result->data[kSha256DigestNumWords + 1] = 0x03040201;
  result->data[kSha256DigestNumWords + 2] = 0x86480165;
  result->data[kSha256DigestNumWords + 3] = 0x0d060960;
  result->data[kSha256DigestNumWords + 4] = 0x00303130;

  return kHmacOk;
}

/**
 * Copies a 3072-bit number from the CPU memory to OTBN data memory.
 *
 * @param otbn The OTBN context object.
 * @param src Source of the data to copy.
 * @param dst Address of the destination in OTBN's data memory.
 * @return The result of the operation.
 */
otbn_error_t write_rsa_3072_int_to_otbn(otbn_t *otbn, const rsa_3072_int_t *src,
                                        otbn_addr_t dst) {
  return otbn_copy_data_to_otbn(otbn, kRsa3072NumWords, src->data, dst);
}

/**
 * Copies a 3072-bit number from OTBN data memory to CPU memory.
 *
 * @param otbn The OTBN context object.
 * @param src The address in OTBN data memory to copy from.
 * @param dst The destination of the copied data in main memory (preallocated).
 * @return The result of the operation.
 */
otbn_error_t read_rsa_3072_int_from_otbn(otbn_t *otbn, otbn_addr_t src,
                                         rsa_3072_int_t *dst) {
  return otbn_copy_data_from_otbn(otbn, kRsa3072NumWords, src, dst->data);
}

// TODO: This implementation waits while OTBN is processing; it should be
// modified to be non-blocking.
otbn_error_t rsa_3072_compute_constants(const rsa_3072_public_key_t *public_key,
                                        rsa_3072_constants_t *result) {
  otbn_t otbn;

  // Initialize OTBN and load the RSA app.
  otbn_init(&otbn);
  OTBN_RETURN_IF_ERROR(otbn_load_app(&otbn, kOtbnAppRsa));

  // Set mode to compute constants.
  OTBN_RETURN_IF_ERROR(otbn_copy_data_to_otbn(
      &otbn, kOtbnRsaModeNumWords, &kOtbnRsaModeConstants, kOtbnVarRsaMode));

  // Set the modulus (n).
  OTBN_RETURN_IF_ERROR(
      write_rsa_3072_int_to_otbn(&otbn, &public_key->n, kOtbnVarRsaInMod));

  // Start the OTBN routine.
  OTBN_RETURN_IF_ERROR(otbn_execute_app(&otbn));

  // Spin here waiting for OTBN to complete.
  OTBN_RETURN_IF_ERROR(otbn_busy_wait_for_done());

  // Read constant rr out of DMEM.
  OTBN_RETURN_IF_ERROR(
      read_rsa_3072_int_from_otbn(&otbn, kOtbnVarRsaRR, &result->rr));

  // Read constant m0_inv out of DMEM.
  OTBN_RETURN_IF_ERROR(otbn_copy_data_from_otbn(
      &otbn, kOtbnWideWordNumWords, kOtbnVarRsaM0Inv, result->m0_inv));

  return kOtbnErrorOk;
}

// TODO: This implementation waits while OTBN is processing; it should be
// modified to be non-blocking.
otbn_error_t rsa_3072_verify(const rsa_3072_int_t *signature,
                             const rsa_3072_int_t *message,
                             const rsa_3072_public_key_t *public_key,
                             const rsa_3072_constants_t *constants,
                             hardened_bool_t *result) {
  // Initially set the result to false in case of early returns due to invalid
  // arguments.
  *result = kHardenedBoolFalse;

  // Only the F4 modulus is supported.
  if (public_key->e != 65537) {
    return kOtbnErrorInvalidArgument;
  }

  // Reject the signature if it is too large (n <= sig): RFC 8017, section
  // 5.2.2, step 1.
  if (memrcmp(public_key->n.data, signature->data, kRsa3072NumBytes) <= 0) {
    return kOtbnErrorInvalidArgument;
  }

  // Initialize OTBN and load the RSA app.
  otbn_t otbn;
  otbn_init(&otbn);
  OTBN_RETURN_IF_ERROR(otbn_load_app(&otbn, kOtbnAppRsa));

  // Set mode to perform modular exponentiation.
  OTBN_RETURN_IF_ERROR(otbn_copy_data_to_otbn(
      &otbn, kOtbnRsaModeNumWords, &kOtbnRsaModeModexp, kOtbnVarRsaMode));

  // Set the modulus (n).
  OTBN_RETURN_IF_ERROR(
      write_rsa_3072_int_to_otbn(&otbn, &public_key->n, kOtbnVarRsaInMod));

  // Set the signature.
  OTBN_RETURN_IF_ERROR(
      write_rsa_3072_int_to_otbn(&otbn, signature, kOtbnVarRsaInBuf));

  // Set the precomputed constant R^2.
  OTBN_RETURN_IF_ERROR(
      write_rsa_3072_int_to_otbn(&otbn, &constants->rr, kOtbnVarRsaRR));

  // Set the precomputed constant m0_inv.
  OTBN_RETURN_IF_ERROR(otbn_copy_data_to_otbn(
      &otbn, kOtbnWideWordNumWords, constants->m0_inv, kOtbnVarRsaM0Inv));

  // Start the OTBN routine.
  OTBN_RETURN_IF_ERROR(otbn_execute_app(&otbn));

  // Spin here waiting for OTBN to complete.
  OTBN_RETURN_IF_ERROR(otbn_busy_wait_for_done());

  // Read recovered message out of OTBN dmem.
  rsa_3072_int_t recoveredMessage;
  OTBN_RETURN_IF_ERROR(
      read_rsa_3072_int_from_otbn(&otbn, kOtbnVarRsaOutBuf, &recoveredMessage));

  // TODO: harden this memory comparison
  // Check if recovered message matches expectation
  *result = kHardenedBoolTrue;
  for (int i = 0; i < kRsa3072NumWords; i++) {
    if (recoveredMessage.data[i] != message->data[i]) {
      *result = kHardenedBoolFalse;
    }
  }

  return kOtbnErrorOk;
}
