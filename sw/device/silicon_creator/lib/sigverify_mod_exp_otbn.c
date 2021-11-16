// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "error.h"
#include "sw/device/silicon_creator/lib/drivers/otbn.h"
#include "sw/device/silicon_creator/lib/otbn_util.h"
#include "sw/device/silicon_creator/lib/sigverify_mod_exp.h"
#include "sw/device/silicon_creator/lib/sigverify_rsa_key.h"

OTBN_DECLARE_APP_SYMBOLS(rsa);          // The OTBN rsa app.
OTBN_DECLARE_PTR_SYMBOL(rsa, mode);     // The RSA mode of operation.
OTBN_DECLARE_PTR_SYMBOL(rsa, n_limbs);  // The number of 256-bit limbs.
OTBN_DECLARE_PTR_SYMBOL(rsa, inout);    // The input/output message buffer
OTBN_DECLARE_PTR_SYMBOL(rsa, modulus);  // The modulus to operate with.

static const otbn_app_t kOtbnAppRsa = OTBN_APP_T_INIT(rsa);
static const otbn_ptr_t kOtbnVarRsaMode = OTBN_PTR_T_INIT(rsa, mode);
static const otbn_ptr_t kOtbnVarRsaNLimbs = OTBN_PTR_T_INIT(rsa, n_limbs);
static const otbn_ptr_t kOtbnVarRsaInOut = OTBN_PTR_T_INIT(rsa, inout);
static const otbn_ptr_t kOtbnVarRsaModulus = OTBN_PTR_T_INIT(rsa, modulus);

static const uint32_t kOtbnModeEncrypt = 1;

/**
 * Runs the OTBN RSA app for sigverify.
 *
 * @param key An RSA public key.
 * @param sig Buffer that holds the signature, little-endian.
 * @param result Buffer to write the result to, little-endian.
 * @return The result of the operation.
 */
otbn_error_t sigverify_mod_exp_otbn_run_app(const sigverify_rsa_key_t *key,
                                            const sigverify_rsa_buffer_t *sig,
                                            sigverify_rsa_buffer_t *result) {
  static const uint32_t n_limbs = kSigVerifyRsaNumBits / 256;

  otbn_t otbn;
  otbn_init(&otbn);
  OTBN_RETURN_IF_ERROR(otbn_load_app(&otbn, kOtbnAppRsa));

  // Set mode so start() will jump into rsa_encrypt().
  // NOLINTNEXTLINE(bugprone-sizeof-expression)
  OTBN_RETURN_IF_ERROR(
      otbn_copy_data_to_otbn(&otbn, sizeof(kOtbnModeEncrypt) / sizeof(uint32_t),
                             &kOtbnModeEncrypt, kOtbnVarRsaMode));  //

  // Set the number of 256-bit limbs for this RSA operation.
  // NOLINTNEXTLINE(bugprone-sizeof-expression)
  OTBN_RETURN_IF_ERROR(otbn_copy_data_to_otbn(
      &otbn, sizeof(n_limbs) / sizeof(uint32_t), &n_limbs, kOtbnVarRsaNLimbs));

  // Set the modulus.
  OTBN_RETURN_IF_ERROR(otbn_copy_data_to_otbn(&otbn, kSigVerifyRsaNumWords,
                                              key->n.data, kOtbnVarRsaModulus));
  // Set the message text.
  OTBN_RETURN_IF_ERROR(otbn_copy_data_to_otbn(&otbn, kSigVerifyRsaNumWords,
                                              sig->data, kOtbnVarRsaInOut));

  // Start the OTBN routine.
  OTBN_RETURN_IF_ERROR(otbn_execute_app(&otbn));

  // Spin here waiting for OTBN to complete.
  OTBN_RETURN_IF_ERROR(otbn_busy_wait_for_done(&otbn));

  // Read digest out of OTBN dmem.
  OTBN_RETURN_IF_ERROR(otbn_copy_data_from_otbn(
      &otbn, kSigVerifyRsaNumWords, kOtbnVarRsaInOut, result->data));
  return kOtbnErrorOk;
}

rom_error_t sigverify_mod_exp_otbn(const sigverify_rsa_key_t *key,
                                   const sigverify_rsa_buffer_t *sig,
                                   sigverify_rsa_buffer_t *result) {
  // TODO: The OTBN routines should be consistent with ibex exponent support.
  if (key->exponent != 65537) {
    return kErrorSigverifyBadExponent;
  }

  // Run OTBN application, and convert the OTBN error to a ROM error if needed.
  FOLD_OTBN_ERROR(sigverify_mod_exp_otbn_run_app(key, sig, result));

  return kErrorOk;
}
