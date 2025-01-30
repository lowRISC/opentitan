// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/lib/sw/device/silicon_creator/sigverify/mod_exp_otbn.h"

#include "sw/device/silicon_creator/lib/drivers/otbn.h"
#include "sw/lib/sw/device/base/macros.h"
#include "sw/lib/sw/device/base/memory.h"
#include "sw/lib/sw/device/silicon_creator/base/sec_mmio.h"
#include "sw/lib/sw/device/silicon_creator/error.h"
#include "sw/lib/sw/device/silicon_creator/sigverify/rsa_key.h"

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

static const sc_otbn_app_t kOtbnAppRsa =
    OTBN_APP_T_INIT(run_rsa_verify_3072_rr_modexp);
static const sc_otbn_addr_t kOtbnVarRsaOutBuf =
    OTBN_ADDR_T_INIT(run_rsa_verify_3072_rr_modexp, out_buf);
static const sc_otbn_addr_t kOtbnVarRsaInMod =
    OTBN_ADDR_T_INIT(run_rsa_verify_3072_rr_modexp, in_mod);
static const sc_otbn_addr_t kOtbnVarRsaInBuf =
    OTBN_ADDR_T_INIT(run_rsa_verify_3072_rr_modexp, in_buf);
static const sc_otbn_addr_t kOtbnVarRsaM0Inv =
    OTBN_ADDR_T_INIT(run_rsa_verify_3072_rr_modexp, m0inv);

/**
 * Copies a 3072-bit number from the CPU memory to OTBN data memory.
 *
 * @param src Source of the data to copy.
 * @param dst Address of the destination in OTBN's data memory.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
static rom_error_t write_rsa_3072_int_to_otbn(const sigverify_rsa_buffer_t *src,
                                              sc_otbn_addr_t dst) {
  return sc_otbn_dmem_write(kSigVerifyRsaNumWords, src->data, dst);
}

/**
 * Copies a 3072-bit number from OTBN data memory to CPU memory.
 *
 * @param src The address in OTBN data memory to copy from.
 * @param dst The destination of the copied data in main memory (preallocated).
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
static rom_error_t read_rsa_3072_int_from_otbn(const sc_otbn_addr_t src,
                                               sigverify_rsa_buffer_t *dst) {
  return sc_otbn_dmem_read(kSigVerifyRsaNumWords, src, dst->data);
}

OT_WARN_UNUSED_RESULT
static rom_error_t run_otbn_rsa_3072_modexp(
    const sigverify_rsa_key_t *public_key,
    const sigverify_rsa_buffer_t *signature,
    sigverify_rsa_buffer_t *recovered_message) {
  // Load the RSA app.
  HARDENED_RETURN_IF_ERROR(sc_otbn_load_app(kOtbnAppRsa));

  // Set the modulus (n).
  HARDENED_RETURN_IF_ERROR(
      write_rsa_3072_int_to_otbn(&public_key->n, kOtbnVarRsaInMod));

  // Set the signature.
  HARDENED_RETURN_IF_ERROR(
      write_rsa_3072_int_to_otbn(signature, kOtbnVarRsaInBuf));

  // Set the precomputed constant m0_inv.
  HARDENED_RETURN_IF_ERROR(sc_otbn_dmem_write(
      kScOtbnWideWordNumWords, public_key->n0_inv, kOtbnVarRsaM0Inv));

  // Start the OTBN routine.
  HARDENED_RETURN_IF_ERROR(sc_otbn_execute());
  SEC_MMIO_WRITE_INCREMENT(kScOtbnSecMmioExecute);

  // Check that the instruction count falls within the expected range. If the
  // instruction count falls outside this range, it indicates that there was a
  // fault injection attack of some kind during OTBN execution.
  uint32_t count = sc_otbn_instruction_count_get();
  if (launder32(count) < kModExpOtbnInsnCountMin ||
      launder32(count) > kModExpOtbnInsnCountMax) {
    return kErrorOtbnBadInsnCount;
  }
  HARDENED_CHECK_GE(count, kModExpOtbnInsnCountMin);
  HARDENED_CHECK_LE(count, kModExpOtbnInsnCountMax);

  // Read recovered message out of OTBN dmem.
  return read_rsa_3072_int_from_otbn(kOtbnVarRsaOutBuf, recovered_message);
}

rom_error_t sigverify_mod_exp_otbn(const sigverify_rsa_key_t *key,
                                   const sigverify_rsa_buffer_t *sig,
                                   sigverify_rsa_buffer_t *result) {
  // Reject the signature if it is too large (n <= sig): RFC 8017, section
  // 5.2.2, step 1.
  if (memrcmp(key->n.data, sig->data, kSigVerifyRsaNumBytes) <= 0) {
    return kErrorSigverifyLargeRsaSignature;
  }

  // Run OTBN application.
  return run_otbn_rsa_3072_modexp(key, sig, result);
}
