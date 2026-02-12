// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/otbn_testutils_rsa.h"

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/dif/dif_otbn.h"
#include "sw/device/lib/testing/otbn_testutils.h"

OTBN_DECLARE_APP_SYMBOLS(run_rsa);
OTBN_DECLARE_SYMBOL_ADDR(run_rsa, mode);
OTBN_DECLARE_SYMBOL_ADDR(run_rsa, inout);
OTBN_DECLARE_SYMBOL_ADDR(run_rsa, rsa_n);
OTBN_DECLARE_SYMBOL_ADDR(run_rsa, rsa_d0);
OTBN_DECLARE_SYMBOL_ADDR(run_rsa, rsa_d1);

static const otbn_app_t kOtbnAppRsa = OTBN_APP_T_INIT(run_rsa);
static const otbn_addr_t kOtbnVarRsaMode = OTBN_ADDR_T_INIT(run_rsa, mode);
static const otbn_addr_t kOtbnVarRsaInOut = OTBN_ADDR_T_INIT(run_rsa, inout);
static const otbn_addr_t kOtbnVarRsaModulus = OTBN_ADDR_T_INIT(run_rsa, rsa_n);
static const otbn_addr_t kOtbnVarRsaD0 = OTBN_ADDR_T_INIT(run_rsa, rsa_d0);
static const otbn_addr_t kOtbnVarRsaD1 = OTBN_ADDR_T_INIT(run_rsa, rsa_d1);

OTBN_DECLARE_SYMBOL_ADDR(run_rsa, MODE_RSA_512_MODEXP);
OTBN_DECLARE_SYMBOL_ADDR(run_rsa, MODE_RSA_512_MODEXP_F4);
OTBN_DECLARE_SYMBOL_ADDR(run_rsa, MODE_RSA_1024_MODEXP);
OTBN_DECLARE_SYMBOL_ADDR(run_rsa, MODE_RSA_1024_MODEXP_F4);
OTBN_DECLARE_SYMBOL_ADDR(run_rsa, MODE_RSA_2048_MODEXP);
OTBN_DECLARE_SYMBOL_ADDR(run_rsa, MODE_RSA_2048_MODEXP_F4);
OTBN_DECLARE_SYMBOL_ADDR(run_rsa, MODE_RSA_3072_MODEXP);
OTBN_DECLARE_SYMBOL_ADDR(run_rsa, MODE_RSA_3072_MODEXP_F4);
OTBN_DECLARE_SYMBOL_ADDR(run_rsa, MODE_RSA_4096_MODEXP);
OTBN_DECLARE_SYMBOL_ADDR(run_rsa, MODE_RSA_4096_MODEXP_F4);
static const uint32_t kMode512Modexp =
    OTBN_ADDR_T_INIT(run_rsa, MODE_RSA_512_MODEXP);
static const uint32_t kMode512ModexpF4 =
    OTBN_ADDR_T_INIT(run_rsa, MODE_RSA_512_MODEXP_F4);
static const uint32_t kMode1024Modexp =
    OTBN_ADDR_T_INIT(run_rsa, MODE_RSA_1024_MODEXP);
static const uint32_t kMode1024ModexpF4 =
    OTBN_ADDR_T_INIT(run_rsa, MODE_RSA_1024_MODEXP_F4);
static const uint32_t kMode2048Modexp =
    OTBN_ADDR_T_INIT(run_rsa, MODE_RSA_2048_MODEXP);
static const uint32_t kMode2048ModexpF4 =
    OTBN_ADDR_T_INIT(run_rsa, MODE_RSA_2048_MODEXP_F4);
static const uint32_t kMode3072Modexp =
    OTBN_ADDR_T_INIT(run_rsa, MODE_RSA_3072_MODEXP);
static const uint32_t kMode3072ModexpF4 =
    OTBN_ADDR_T_INIT(run_rsa, MODE_RSA_3072_MODEXP_F4);
static const uint32_t kMode4096Modexp =
    OTBN_ADDR_T_INIT(run_rsa, MODE_RSA_4096_MODEXP);
static const uint32_t kMode4096ModexpF4 =
    OTBN_ADDR_T_INIT(run_rsa, MODE_RSA_4096_MODEXP_F4);

enum { kOtbnWideWordBytes = 256 / 8 };

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

  uint32_t mode;
  switch (size_bytes) {
    case 64:
      mode = kMode512ModexpF4;
      break;
    case 128:
      mode = kMode1024ModexpF4;
      break;
    case 256:
      mode = kMode2048ModexpF4;
      break;
    case 384:
      mode = kMode3072ModexpF4;
      break;
    case 512:
      mode = kMode4096ModexpF4;
      break;
    default:
      return INVALID_ARGUMENT();
  };

  // Write input arguments.
  TRY(otbn_testutils_write_data(otbn, sizeof(uint32_t), &mode,
                                kOtbnVarRsaMode));
  TRY(otbn_testutils_write_data(otbn, size_bytes, modulus, kOtbnVarRsaModulus));
  TRY(otbn_testutils_write_data(otbn, size_bytes, in, kOtbnVarRsaInOut));

  // Call OTBN to start the operation.
  return otbn_testutils_execute(otbn);
}

status_t otbn_testutils_rsa_modexp_consttime_start(
    dif_otbn_t *otbn, const uint8_t *modulus, const uint8_t *d_share0,
    const uint8_t *d_share1, const uint8_t *in, size_t size_bytes) {
  if (otbn == NULL || size_bytes % kOtbnWideWordBytes != 0) {
    return INVALID_ARGUMENT();
  }

  uint32_t mode;
  switch (size_bytes) {
    case 64:
      mode = kMode512Modexp;
      break;
    case 128:
      mode = kMode1024Modexp;
      break;
    case 256:
      mode = kMode2048Modexp;
      break;
    case 384:
      mode = kMode3072Modexp;
      break;
    case 512:
      mode = kMode4096Modexp;
      break;
    default:
      return INVALID_ARGUMENT();
  };

  // Write input arguments.
  TRY(otbn_testutils_write_data(otbn, sizeof(uint32_t), &mode,
                                kOtbnVarRsaMode));
  TRY(otbn_testutils_write_data(otbn, size_bytes, modulus, kOtbnVarRsaModulus));
  TRY(otbn_testutils_write_data(otbn, size_bytes, d_share0, kOtbnVarRsaD0));
  TRY(otbn_testutils_write_data(otbn, size_bytes, d_share1, kOtbnVarRsaD1));
  TRY(otbn_testutils_write_data(otbn, size_bytes, in, kOtbnVarRsaInOut));

  // Call OTBN to start the operation.
  return otbn_testutils_execute(otbn);
}

static status_t modexp_finalize(dif_otbn_t *otbn, uint8_t *out,
                                size_t size_bytes) {
  if (otbn == NULL || size_bytes % kOtbnWideWordBytes != 0) {
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
