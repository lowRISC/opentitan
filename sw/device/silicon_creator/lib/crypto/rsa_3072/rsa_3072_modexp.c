// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/crypto/rsa_3072/rsa_3072_modexp.h"

#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/silicon_creator/lib/drivers/otbn.h"
#include "sw/device/silicon_creator/lib/otbn_util.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

OTBN_DECLARE_APP_SYMBOLS(rsa_3072_modexp);  // The OTBN RSA-3072 verify app.
OTBN_DECLARE_PTR_SYMBOL(rsa_3072_modexp, out_buf);  // Output buffer (message).
OTBN_DECLARE_PTR_SYMBOL(rsa_3072_modexp, in_mod);   // The RSA modulus (n).
OTBN_DECLARE_PTR_SYMBOL(rsa_3072_modexp, in_buf);   // The signature (s).
OTBN_DECLARE_PTR_SYMBOL(rsa_3072_modexp,
                        in_m0inv);  // The Montgomery constant m0_inv.

static const otbn_app_t kOtbnAppRsa = OTBN_APP_T_INIT(rsa_3072_modexp);
static const otbn_ptr_t kOtbnVarRsaOutBuf =
    OTBN_PTR_T_INIT(rsa_3072_modexp, out_buf);
static const otbn_ptr_t kOtbnVarRsaInMod =
    OTBN_PTR_T_INIT(rsa_3072_modexp, in_mod);
static const otbn_ptr_t kOtbnVarRsaInBuf =
    OTBN_PTR_T_INIT(rsa_3072_modexp, in_buf);
static const otbn_ptr_t kOtbnVarRsaInM0Inv =
    OTBN_PTR_T_INIT(rsa_3072_modexp, in_m0inv);

/**
 * Copies a 3072-bit number from the CPU memory to OTBN data memory.
 *
 * @param otbn The OTBN context object.
 * @param src Source of the data to copy.
 * @param dst Pointer to the destination in OTBN's data memory.
 * @return The result of the operation.
 */
static otbn_error_t write_rsa_3072_int_to_otbn(otbn_t *otbn,
                                               const rsa_3072_int_t *src,
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
static otbn_error_t read_rsa_3072_int_from_otbn(otbn_t *otbn,
                                                const otbn_ptr_t src,
                                                rsa_3072_int_t *dst) {
  return otbn_copy_data_from_otbn(otbn, kRsa3072NumWords, src, dst->data);
}

otbn_error_t run_otbn_rsa_3072_modexp(const rsa_3072_int_t *signature,
                                      const rsa_3072_public_key_t *public_key,
                                      const uint32_t *m0_inv,
                                      rsa_3072_int_t *recovered_message) {
  otbn_t otbn;

  // For now, only the F4 modulus is supported.
  if (public_key->e != 65537) {
    return kOtbnErrorInvalidArgument;
  }

  // Initialize OTBN and load the RSA app.
  otbn_init(&otbn);
  OTBN_RETURN_IF_ERROR(otbn_load_app(&otbn, kOtbnAppRsa));

  // Set the modulus (n).
  OTBN_RETURN_IF_ERROR(
      write_rsa_3072_int_to_otbn(&otbn, &public_key->n, kOtbnVarRsaInMod));

  // Set the signature.
  OTBN_RETURN_IF_ERROR(
      write_rsa_3072_int_to_otbn(&otbn, signature, kOtbnVarRsaInBuf));

  // Set the precomputed constant m0_inv.
  OTBN_RETURN_IF_ERROR(otbn_copy_data_to_otbn(&otbn, kOtbnWideWordNumWords,
                                              m0_inv, kOtbnVarRsaInM0Inv));

  // Start the OTBN routine.
  OTBN_RETURN_IF_ERROR(otbn_execute_app(&otbn));

  // Spin here waiting for OTBN to complete.
  OTBN_RETURN_IF_ERROR(otbn_busy_wait_for_done(&otbn));

  // Read recovered message out of OTBN dmem.
  OTBN_RETURN_IF_ERROR(
      read_rsa_3072_int_from_otbn(&otbn, kOtbnVarRsaOutBuf, recovered_message));

  return kOtbnErrorOk;
}
