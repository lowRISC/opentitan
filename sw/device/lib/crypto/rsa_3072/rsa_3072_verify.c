// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/crypto/rsa_3072/rsa_3072_verify.h"

#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/silicon_creator/lib/drivers/hmac.h"
#include "sw/device/silicon_creator/lib/drivers/otbn.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/lib/otbn_util.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

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
static const uint32_t kOtbnRsaModeNumWords = 1;
static const uint32_t kOtbnRsaModeConstants = 1;
static const uint32_t kOtbnRsaModeModexp = 2;

rom_error_t rsa_3072_encode_sha256(const uint8_t *msg, size_t msgLen,
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
  if (msg != NULL) {
    RETURN_IF_ERROR(hmac_sha256_update(msg, msgLen));
  }
  hmac_digest_t digest;
  RETURN_IF_ERROR(hmac_sha256_final(&digest));

  // Copy the message digest into the least significant end of the result.
  memcpy(result->data, digest.digest, sizeof(digest.digest));

  // Set remainder of 0x00 || T section
  result->data[kSha256DigestNumWords] = 0x05000420;
  result->data[kSha256DigestNumWords + 1] = 0x03040201;
  result->data[kSha256DigestNumWords + 2] = 0x86480165;
  result->data[kSha256DigestNumWords + 3] = 0x0d060960;
  result->data[kSha256DigestNumWords + 4] = 0x00303130;

  return kErrorOk;
}

/**
 * Copies a 3072-bit number from the CPU memory to OTBN data memory.
 *
 * @param otbn The OTBN context object.
 * @param src Source of the data to copy.
 * @param dst Pointer to the destination in OTBN's data memory.
 * @return The result of the operation.
 */
otbn_error_t write_rsa_3072_int_to_otbn(otbn_t *otbn, const rsa_3072_int_t *src,
                                        otbn_ptr_t dst) {
  return otbn_copy_data_to_otbn(otbn, kRsa3072NumWords, src->data, dst);
}

/**
 * Copies a 3072-bit number from OTBN data memory to CPU memory.
 *
 * @param otbn The OTBN context object.
 * @param src The pointer in OTBN data memory to copy from.
 * @param dst The destination of the copied data in main memory (preallocated).
 * @return The result of the operation.
 */
otbn_error_t read_rsa_3072_int_from_otbn(otbn_t *otbn, const otbn_ptr_t src,
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
  OTBN_RETURN_IF_ERROR(otbn_busy_wait_for_done(&otbn));

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
  otbn_t otbn;
  rsa_3072_int_t recoveredMessage;

  // For now, only the F4 modulus is supported.
  if (public_key->e != 65537) {
    return kOtbnErrorInvalidArgument;
  }

  // TODO: Check that s < n, reject signature otherwise

  // Initialize OTBN and load the RSA app.
  otbn_init(&otbn);
  OTBN_RETURN_IF_ERROR(otbn_load_app(&otbn, kOtbnAppRsa));

  // Set mode to perform modular exponentiation.
  OTBN_RETURN_IF_ERROR(otbn_copy_data_to_otbn(
      &otbn, kOtbnRsaModeNumWords, &kOtbnRsaModeModexp, kOtbnVarRsaMode));

  // Set the exponent (e).
  OTBN_RETURN_IF_ERROR(
      otbn_copy_data_to_otbn(&otbn, 1, &public_key->e, kOtbnVarRsaInExp));

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
  OTBN_RETURN_IF_ERROR(otbn_busy_wait_for_done(&otbn));

  // Read recovered message out of OTBN dmem.
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
