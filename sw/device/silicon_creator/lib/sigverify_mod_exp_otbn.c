// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/silicon_creator/lib/drivers/otbn.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/lib/otbn_util.h"
#include "sw/device/silicon_creator/lib/sigverify_mod_exp.h"
#include "sw/device/silicon_creator/lib/sigverify_rsa_key.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

OTBN_DECLARE_APP_SYMBOLS(
    run_rsa_verify_3072_rr_modexp);  // The OTBN RSA-3072 app.
OTBN_DECLARE_PTR_SYMBOL(run_rsa_verify_3072_rr_modexp,
                        exp);  // The RSA key exponent (e).
OTBN_DECLARE_PTR_SYMBOL(run_rsa_verify_3072_rr_modexp,
                        dptr_out_buf);  // Output buffer (message).
OTBN_DECLARE_PTR_SYMBOL(run_rsa_verify_3072_rr_modexp,
                        dptr_mod);  // The RSA modulus (n).
OTBN_DECLARE_PTR_SYMBOL(run_rsa_verify_3072_rr_modexp,
                        dptr_sig);  // The signature (s).
OTBN_DECLARE_PTR_SYMBOL(run_rsa_verify_3072_rr_modexp,
                        dptr_rr);  // The Montgomery constant R^2.
OTBN_DECLARE_PTR_SYMBOL(run_rsa_verify_3072_rr_modexp,
                        dptr_m0inv);  // The Montgomery constant m0_inv.

static const otbn_app_t kOtbnAppRsa =
    OTBN_APP_T_INIT(run_rsa_verify_3072_rr_modexp);
static const otbn_ptr_t kOtbnVarRsaExp =
    OTBN_PTR_T_INIT(run_rsa_verify_3072_rr_modexp, exp);
static const otbn_ptr_t kOtbnVarRsaDptrOutBuf =
    OTBN_PTR_T_INIT(run_rsa_verify_3072_rr_modexp, dptr_out_buf);
static const otbn_ptr_t kOtbnVarRsaDptrMod =
    OTBN_PTR_T_INIT(run_rsa_verify_3072_rr_modexp, dptr_mod);
static const otbn_ptr_t kOtbnVarRsaDptrSig =
    OTBN_PTR_T_INIT(run_rsa_verify_3072_rr_modexp, dptr_sig);
static const otbn_ptr_t kOtbnVarRsaDptrRR =
    OTBN_PTR_T_INIT(run_rsa_verify_3072_rr_modexp, dptr_rr);
static const otbn_ptr_t kOtbnVarRsaDptrM0Inv =
    OTBN_PTR_T_INIT(run_rsa_verify_3072_rr_modexp, dptr_m0inv);

otbn_error_t run_otbn_rsa_3072_modexp(
    const sigverify_rsa_key_t *public_key,
    const sigverify_rsa_buffer_t *signature,
    sigverify_rsa_buffer_t *recovered_message) {
  otbn_t otbn;

  // Initialize OTBN and load the RSA app.
  otbn_init(&otbn);
  OTBN_RETURN_IF_ERROR(otbn_load_app(&otbn, kOtbnAppRsa));

  // Set the exponent (e).
  OTBN_RETURN_IF_ERROR(
      otbn_copy_data_to_otbn(&otbn, 1, &public_key->exponent, kOtbnVarRsaExp));

  // Set the modulus.
  OTBN_RETURN_IF_ERROR(otbn_dmem_write_indirect(
      &otbn, kSigVerifyRsaNumWords, public_key->n.data, kOtbnVarRsaDptrMod));

  // Set the signature.
  OTBN_RETURN_IF_ERROR(otbn_dmem_write_indirect(
      &otbn, kSigVerifyRsaNumWords, signature->data, kOtbnVarRsaDptrSig));

  // Set the precomputed constant m0_inv.
  OTBN_RETURN_IF_ERROR(otbn_dmem_write_indirect(
      &otbn, kOtbnWideWordNumWords, public_key->n0_inv, kOtbnVarRsaDptrM0Inv));

  // Allocate a buffer for the constant R^2.
  OTBN_RETURN_IF_ERROR(
      otbn_dmem_alloc(&otbn, kSigVerifyRsaNumWords, kOtbnVarRsaDptrRR));

  // Allocate a buffer for the output.
  OTBN_RETURN_IF_ERROR(
      otbn_dmem_alloc(&otbn, kSigVerifyRsaNumWords, kOtbnVarRsaDptrOutBuf));

  // Start the OTBN routine.
  OTBN_RETURN_IF_ERROR(otbn_execute_app(&otbn));

  // Spin here waiting for OTBN to complete.
  OTBN_RETURN_IF_ERROR(otbn_busy_wait_for_done(&otbn));

  // Read recovered message out of OTBN dmem.
  OTBN_RETURN_IF_ERROR(otbn_dmem_read_indirect(&otbn, kSigVerifyRsaNumWords,
                                               kOtbnVarRsaDptrOutBuf,
                                               recovered_message->data));

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
  FOLD_OTBN_ERROR(run_otbn_rsa_3072_modexp(key, sig, result));

  return kErrorOk;
}
