// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/otbn_testutils_rsa.h"

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/dif/dif_otbn.h"
#include "sw/device/lib/testing/otbn_testutils.h"

OTBN_DECLARE_APP_SYMBOLS(rsa);
OTBN_DECLARE_SYMBOL_ADDR(rsa, mode);
OTBN_DECLARE_SYMBOL_ADDR(rsa, n_limbs);
OTBN_DECLARE_SYMBOL_ADDR(rsa, inout);
OTBN_DECLARE_SYMBOL_ADDR(rsa, modulus);
OTBN_DECLARE_SYMBOL_ADDR(rsa, exp);

static const otbn_app_t kOtbnAppRsa = OTBN_APP_T_INIT(rsa);
static const otbn_addr_t kOtbnVarRsaMode = OTBN_ADDR_T_INIT(rsa, mode);
static const otbn_addr_t kOtbnVarRsaNLimbs = OTBN_ADDR_T_INIT(rsa, n_limbs);
static const otbn_addr_t kOtbnVarRsaInOut = OTBN_ADDR_T_INIT(rsa, inout);
static const otbn_addr_t kOtbnVarRsaModulus = OTBN_ADDR_T_INIT(rsa, modulus);
static const otbn_addr_t kOtbnVarRsaExp = OTBN_ADDR_T_INIT(rsa, exp);

enum {
  kOtbnWideWordBytes = 256 / 8,
  kModeEncrypt = 1,
  kModeDecrypt = 2,
};

status_t otbn_testutils_rsa_load(dif_otbn_t *otbn) {
  if (otbn == NULL) {
    return INVALID_ARGUMENT();
  }
  return otbn_testutils_load_app(otbn, kOtbnAppRsa);
}

status_t otbn_testutils_rsa_modexp_f4_start(dif_otbn_t *otbn,
                                            const uint8_t *modulus,
                                            const uint8_t *in,
                                            size_t size_bytes) {
  if (otbn == NULL || size_bytes % kOtbnWideWordBytes != 0) {
    return INVALID_ARGUMENT();
  }

  uint32_t n_limbs = size_bytes / kOtbnWideWordBytes;
  if (n_limbs == 0 || n_limbs > 16) {
    return INVALID_ARGUMENT();
  }

  // Write input arguments.
  uint32_t mode = kModeEncrypt;
  TRY(otbn_testutils_write_data(otbn, sizeof(uint32_t), &mode,
                                kOtbnVarRsaMode));
  TRY(otbn_testutils_write_data(otbn, sizeof(uint32_t), &n_limbs,
                                kOtbnVarRsaNLimbs));
  TRY(otbn_testutils_write_data(otbn, size_bytes, modulus, kOtbnVarRsaModulus));
  TRY(otbn_testutils_write_data(otbn, size_bytes, in, kOtbnVarRsaInOut));

  // Call OTBN to start the operation.
  return otbn_testutils_execute(otbn);
}

status_t otbn_testutils_rsa_modexp_consttime_start(
    dif_otbn_t *otbn, const uint8_t *modulus, const uint8_t *private_exponent,
    const uint8_t *in, size_t size_bytes) {
  if (otbn == NULL || size_bytes % kOtbnWideWordBytes != 0) {
    return INVALID_ARGUMENT();
  }

  uint32_t n_limbs = size_bytes / kOtbnWideWordBytes;
  if (n_limbs == 0 || n_limbs > 16) {
    return INVALID_ARGUMENT();
  }

  // Write input arguments.
  uint32_t mode = kModeDecrypt;
  TRY(otbn_testutils_write_data(otbn, sizeof(mode), &mode, kOtbnVarRsaMode));
  TRY(otbn_testutils_write_data(otbn, sizeof(n_limbs), &n_limbs,
                                kOtbnVarRsaNLimbs));
  TRY(otbn_testutils_write_data(otbn, size_bytes, modulus, kOtbnVarRsaModulus));
  TRY(otbn_testutils_write_data(otbn, size_bytes, private_exponent,
                                kOtbnVarRsaExp));
  TRY(otbn_testutils_write_data(otbn, size_bytes, in, kOtbnVarRsaInOut));

  // Call OTBN to start the operation.
  return otbn_testutils_execute(otbn);
}

static status_t modexp_finalize(dif_otbn_t *otbn, uint8_t *out,
                                size_t size_bytes) {
  if (otbn == NULL || size_bytes % kOtbnWideWordBytes != 0) {
    return INVALID_ARGUMENT();
  }

  uint32_t n_limbs = size_bytes / kOtbnWideWordBytes;
  if (n_limbs == 0 || n_limbs > 16) {
    return INVALID_ARGUMENT();
  }

  // Wait for OTBN to complete.
  TRY(otbn_testutils_wait_for_done(otbn, kDifOtbnErrBitsNoError));

  // Read back results.
  return otbn_testutils_read_data(otbn, size_bytes, kOtbnVarRsaInOut, out);
}

status_t otbn_testutils_rsa_modexp_f4_finalize(dif_otbn_t *otbn, uint8_t *out,
                                               size_t size_bytes) {
  return modexp_finalize(otbn, out, size_bytes);
}

status_t otbn_testutils_rsa_modexp_consttime_finalize(dif_otbn_t *otbn,
                                                      uint8_t *out,
                                                      size_t size_bytes) {
  return modexp_finalize(otbn, out, size_bytes);
}
