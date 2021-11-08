// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/crypto/rsa_3072/rsa_3072_verify.h"

#include "sw/device/lib/base/hardened.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/lib/otbn_util.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

OTBN_DECLARE_APP_SYMBOLS(rsa_3072_verify);  // The OTBN RSA-3072 verify app.
OTBN_DECLARE_PTR_SYMBOL(rsa_3072_verify, mode);     // Mode (precomp or verify).
OTBN_DECLARE_PTR_SYMBOL(rsa_3072_verify, out_buf);  // Output buffer (message).
OTBN_DECLARE_PTR_SYMBOL(rsa_3072_verify, in_mod);   // The RSA modulus (n).
OTBN_DECLARE_PTR_SYMBOL(rsa_3072_verify, in_buf);   // The signature (s).
OTBN_DECLARE_PTR_SYMBOL(rsa_3072_verify,
                        in_rr);  // The Montgomery constant R^2.
OTBN_DECLARE_PTR_SYMBOL(rsa_3072_verify,
                        in_m0inv);  // The Montgomery constant m0_inv.

static const otbn_app_t kOtbnAppRsa = OTBN_APP_T_INIT(rsa_3072_verify);
static const otbn_ptr_t kOtbnVarRsaMode =
    OTBN_PTR_T_INIT(rsa_3072_verify, mode);
static const otbn_ptr_t kOtbnVarRsaOutBuf =
    OTBN_PTR_T_INIT(rsa_3072_verify, out_buf);
static const otbn_ptr_t kOtbnVarRsaInMod =
    OTBN_PTR_T_INIT(rsa_3072_verify, in_mod);
static const otbn_ptr_t kOtbnVarRsaInBuf =
    OTBN_PTR_T_INIT(rsa_3072_verify, in_buf);
static const otbn_ptr_t kOtbnVarRsaInRR =
    OTBN_PTR_T_INIT(rsa_3072_verify, in_rr);
static const otbn_ptr_t kOtbnVarRsaInM0Inv =
    OTBN_PTR_T_INIT(rsa_3072_verify, in_m0inv);

/* Mode is represented by a single word, 1 for precomputation and 2 for verify
 */
static const uint32_t kOtbnRsaModeNumWords = 1;
static const uint32_t kOtbnRsaModeVerify = 1;
static const uint32_t kOtbnRsaModeComputeRR = 2;
static const uint32_t kOtbnRsaModeComputeM0Inv = 3;

/**
 * Copies a 3072-bit number from the CPU memory to OTBN data memory.
 *
 * @param otbn The OTBN context object.
 * @param src Source of the data to copy.
 * @param dst Pointer to the destination in OTBN's data memory.
 * @return The result of the operation.
 */
rom_error_t write_rsa_3072_int_to_otbn(otbn_t *otbn, const rsa_3072_int_t *src,
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
rom_error_t read_rsa_3072_int_from_otbn(otbn_t *otbn, const otbn_ptr_t src,
                                        rsa_3072_int_t *dst) {
  return otbn_copy_data_from_otbn(otbn, kRsa3072NumWords, src, dst->data);
}

// TODO: This implementation waits while OTBN is processing; it should be
// modified to be non-blocking.
rom_error_t rsa_3072_compute_rr(const rsa_3072_public_key_t *public_key,
                                rsa_3072_int_t *result) {
  otbn_t otbn;

  // Initialize OTBN and load the RSA app.
  otbn_init(&otbn);
  RETURN_IF_ERROR(otbn_load_app(&otbn, kOtbnAppRsa));

  // Set mode to compute R^2.
  RETURN_IF_ERROR(otbn_copy_data_to_otbn(
      &otbn, kOtbnRsaModeNumWords, &kOtbnRsaModeComputeRR, kOtbnVarRsaMode));

  // Set the modulus (n).
  RETURN_IF_ERROR(
      write_rsa_3072_int_to_otbn(&otbn, &public_key->n, kOtbnVarRsaInMod));

  // Start the OTBN routine.
  RETURN_IF_ERROR(otbn_execute_app(&otbn));

  // Spin here waiting for OTBN to complete.
  RETURN_IF_ERROR(otbn_busy_wait_for_done(&otbn));

  // Read constant rr out of DMEM.
  RETURN_IF_ERROR(read_rsa_3072_int_from_otbn(&otbn, kOtbnVarRsaInRR, result));

  return kErrorOk;
}

// TODO: This implementation waits while OTBN is processing; it should be
// modified to be non-blocking.
rom_error_t rsa_3072_compute_m0_inv(const rsa_3072_public_key_t *public_key,
                                    uint32_t result[kOtbnWideWordNumWords]) {
  otbn_t otbn;

  // Initialize OTBN and load the RSA app.
  otbn_init(&otbn);
  RETURN_IF_ERROR(otbn_load_app(&otbn, kOtbnAppRsa));

  // Set mode to compute m0_inv.
  RETURN_IF_ERROR(otbn_copy_data_to_otbn(
      &otbn, kOtbnRsaModeNumWords, &kOtbnRsaModeComputeM0Inv, kOtbnVarRsaMode));

  // Set the modulus (n).
  RETURN_IF_ERROR(
      write_rsa_3072_int_to_otbn(&otbn, &public_key->n, kOtbnVarRsaInMod));

  // Start the OTBN routine.
  RETURN_IF_ERROR(otbn_execute_app(&otbn));

  // Spin here waiting for OTBN to complete.
  RETURN_IF_ERROR(otbn_busy_wait_for_done(&otbn));

  // Read precomputed constant m0_inv out of DMEM.
  RETURN_IF_ERROR(otbn_copy_data_from_otbn(&otbn, kOtbnWideWordNumWords,
                                           kOtbnVarRsaInM0Inv, result));

  return kErrorOk;
}

// TODO: This implementation waits while OTBN is processing; it should be
// modified to be non-blocking.
rom_error_t rsa_3072_compute_constants(const rsa_3072_public_key_t *public_key,
                                       rsa_3072_constants_t *result) {
  RETURN_IF_ERROR(rsa_3072_compute_rr(public_key, &result->rr));
  RETURN_IF_ERROR(rsa_3072_compute_m0_inv(public_key, result->m0_inv));

  return kErrorOk;
}

// TODO: This implementation waits while OTBN is processing; it should be
// modified to be non-blocking.
rom_error_t rsa_3072_verify(const rsa_3072_int_t *signature,
                            const rsa_3072_int_t *message,
                            const rsa_3072_public_key_t *public_key,
                            const rsa_3072_constants_t *constants,
                            hardened_bool_t *result) {
  otbn_t otbn;
  rsa_3072_int_t recoveredMessage;

  // For now, only the F4 modulus is supported.
  if (public_key->e != 65537) {
    return kErrorOtbnInvalidArgument;
  }

  // TODO: Check that s < n, reject signature otherwise

  // Initialize OTBN and load the RSA app.
  otbn_init(&otbn);
  RETURN_IF_ERROR(otbn_load_app(&otbn, kOtbnAppRsa));

  // Set mode to perform verification.
  RETURN_IF_ERROR(otbn_copy_data_to_otbn(&otbn, kOtbnRsaModeNumWords,
                                         &kOtbnRsaModeVerify, kOtbnVarRsaMode));

  // Set the modulus (n).
  RETURN_IF_ERROR(
      write_rsa_3072_int_to_otbn(&otbn, &public_key->n, kOtbnVarRsaInMod));

  // Set the signature.
  RETURN_IF_ERROR(
      write_rsa_3072_int_to_otbn(&otbn, signature, kOtbnVarRsaInBuf));

  // Set the precomputed constant R^2.
  RETURN_IF_ERROR(
      write_rsa_3072_int_to_otbn(&otbn, &constants->rr, kOtbnVarRsaInRR));

  // Set the precomputed constant m0_inv.
  RETURN_IF_ERROR(otbn_copy_data_to_otbn(
      &otbn, kOtbnWideWordNumWords, constants->m0_inv, kOtbnVarRsaInM0Inv));

  // Start the OTBN routine.
  RETURN_IF_ERROR(otbn_execute_app(&otbn));

  // Spin here waiting for OTBN to complete.
  RETURN_IF_ERROR(otbn_busy_wait_for_done(&otbn));

  // Read recovered message out of OTBN dmem.
  RETURN_IF_ERROR(
      read_rsa_3072_int_from_otbn(&otbn, kOtbnVarRsaOutBuf, &recoveredMessage));

  // TODO: harden this memory comparison
  // Check if recovered message matches expectation
  *result = kHardenedBoolTrue;
  for (int i = 0; i < kRsa3072NumWords; i++) {
    if (recoveredMessage.data[i] != message->data[i]) {
      *result = kHardenedBoolFalse;
    }
  }

  return kErrorOk;
}
