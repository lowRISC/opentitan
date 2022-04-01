// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/sigverify/sigverify_mod_exp_otbn.h"

#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/silicon_creator/lib/drivers/otbn.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/lib/otbn_util.h"
#include "sw/device/silicon_creator/lib/sigverify/sigverify_rsa_key.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

OTBN_DECLARE_APP_SYMBOLS(
    run_rsa_verify_3072_rr_modexp);  // The OTBN RSA-3072 app.
OTBN_DECLARE_SYMBOL_ADDR(run_rsa_verify_3072_rr_modexp,
                         out_buf);  // Output buffer (message).
OTBN_DECLARE_SYMBOL_ADDR(run_rsa_verify_3072_rr_modexp,
                         in_mod);  // The RSA modulus (n).
OTBN_DECLARE_SYMBOL_ADDR(run_rsa_verify_3072_rr_modexp,
                         in_buf);  // The signature (s).
OTBN_DECLARE_SYMBOL_ADDR(run_rsa_verify_3072_rr_modexp,
                         m0inv);  // The Montgomery constant m0_inv.

static const otbn_app_t kOtbnAppRsa =
    OTBN_APP_T_INIT(run_rsa_verify_3072_rr_modexp);
static const otbn_addr_t kOtbnVarRsaOutBuf =
    OTBN_ADDR_T_INIT(run_rsa_verify_3072_rr_modexp, out_buf);
static const otbn_addr_t kOtbnVarRsaInMod =
    OTBN_ADDR_T_INIT(run_rsa_verify_3072_rr_modexp, in_mod);
static const otbn_addr_t kOtbnVarRsaInBuf =
    OTBN_ADDR_T_INIT(run_rsa_verify_3072_rr_modexp, in_buf);
static const otbn_addr_t kOtbnVarRsaM0Inv =
    OTBN_ADDR_T_INIT(run_rsa_verify_3072_rr_modexp, m0inv);

/**
 * Copies a 3072-bit number from the CPU memory to OTBN data memory.
 *
 * @param otbn The OTBN context object.
 * @param src Source of the data to copy.
 * @param dst Address of the destination in OTBN's data memory.
 * @return The result of the operation.
 */
static rom_error_t write_rsa_3072_int_to_otbn(otbn_t *otbn,
                                              const sigverify_rsa_buffer_t *src,
                                              otbn_addr_t dst) {
  return otbn_copy_data_to_otbn(otbn, kSigVerifyRsaNumWords, src->data, dst);
}

/**
 * Copies a 3072-bit number from OTBN data memory to CPU memory.
 *
 * @param otbn The OTBN context object.
 * @param src The address in OTBN data memory to copy from.
 * @param dst The destination of the copied data in main memory (preallocated).
 * @return The result of the operation.
 */
static rom_error_t read_rsa_3072_int_from_otbn(otbn_t *otbn,
                                               const otbn_addr_t src,
                                               sigverify_rsa_buffer_t *dst) {
  return otbn_copy_data_from_otbn(otbn, kSigVerifyRsaNumWords, src, dst->data);
}

rom_error_t run_otbn_rsa_3072_modexp(
    const sigverify_rsa_key_t *public_key,
    const sigverify_rsa_buffer_t *signature,
    sigverify_rsa_buffer_t *recovered_message) {
  otbn_t otbn;

  // Initialize OTBN and load the RSA app.
  otbn_init(&otbn);
  RETURN_IF_ERROR(otbn_load_app(&otbn, kOtbnAppRsa));

  // Set the modulus (n).
  RETURN_IF_ERROR(
      write_rsa_3072_int_to_otbn(&otbn, &public_key->n, kOtbnVarRsaInMod));

  // Set the signature.
  RETURN_IF_ERROR(
      write_rsa_3072_int_to_otbn(&otbn, signature, kOtbnVarRsaInBuf));

  // Set the precomputed constant m0_inv.
  RETURN_IF_ERROR(otbn_copy_data_to_otbn(&otbn, kOtbnWideWordNumWords,
                                         public_key->n0_inv, kOtbnVarRsaM0Inv));

  // Start the OTBN routine.
  RETURN_IF_ERROR(otbn_execute_app(&otbn));

  // Spin here waiting for OTBN to complete.
  RETURN_IF_ERROR(otbn_busy_wait_for_done(&otbn));

  // Read recovered message out of OTBN dmem.
  RETURN_IF_ERROR(
      read_rsa_3072_int_from_otbn(&otbn, kOtbnVarRsaOutBuf, recovered_message));

  return kErrorOk;
}

rom_error_t sigverify_mod_exp_otbn(const sigverify_rsa_key_t *key,
                                   const sigverify_rsa_buffer_t *sig,
                                   sigverify_rsa_buffer_t *result) {
  // Reject the signature if it is too large (n <= sig): RFC 8017, section
  // 5.2.2, step 1.
  if (memrcmp(key->n.data, sig->data, kSigVerifyRsaNumBytes) <= 0) {
    return kErrorSigverifyBadSignature;
  }

  // Run OTBN application.
  RETURN_IF_ERROR(run_otbn_rsa_3072_modexp(key, sig, result));

  return kErrorOk;
}
