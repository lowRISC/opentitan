// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/impl/rsa/rsa_modexp.h"

#include "sw/device/lib/crypto/drivers/otbn.h"

// Module ID for status codes.
#define MODULE_ID MAKE_MODULE_ID('r', 'm', 'e')

// Declare the OTBN app.
OTBN_DECLARE_APP_SYMBOLS(run_rsa_modexp);
static const otbn_app_t kOtbnAppRsaModexp = OTBN_APP_T_INIT(run_rsa_modexp);

// Declare offsets for input and output buffers.
OTBN_DECLARE_SYMBOL_ADDR(run_rsa_modexp, mode);   // Application mode.
OTBN_DECLARE_SYMBOL_ADDR(run_rsa_modexp, n);      // Public modulus n.
OTBN_DECLARE_SYMBOL_ADDR(run_rsa_modexp, d);      // Private exponent d.
OTBN_DECLARE_SYMBOL_ADDR(run_rsa_modexp, inout);  // Input/output buffer.

static const otbn_addr_t kOtbnVarRsaMode =
    OTBN_ADDR_T_INIT(run_rsa_modexp, mode);
static const otbn_addr_t kOtbnVarRsaN = OTBN_ADDR_T_INIT(run_rsa_modexp, n);
static const otbn_addr_t kOtbnVarRsaD = OTBN_ADDR_T_INIT(run_rsa_modexp, d);
static const otbn_addr_t kOtbnVarRsaInOut =
    OTBN_ADDR_T_INIT(run_rsa_modexp, inout);

// Declare mode constants.
OTBN_DECLARE_SYMBOL_ADDR(run_rsa_modexp, MODE_RSA_2048_MODEXP);
OTBN_DECLARE_SYMBOL_ADDR(run_rsa_modexp, MODE_RSA_2048_MODEXP_F4);
OTBN_DECLARE_SYMBOL_ADDR(run_rsa_modexp, MODE_RSA_3072_MODEXP);
OTBN_DECLARE_SYMBOL_ADDR(run_rsa_modexp, MODE_RSA_3072_MODEXP_F4);
OTBN_DECLARE_SYMBOL_ADDR(run_rsa_modexp, MODE_RSA_4096_MODEXP);
OTBN_DECLARE_SYMBOL_ADDR(run_rsa_modexp, MODE_RSA_4096_MODEXP_F4);
static const uint32_t kMode2048Modexp =
    OTBN_ADDR_T_INIT(run_rsa_modexp, MODE_RSA_2048_MODEXP);
static const uint32_t kMode2048ModexpF4 =
    OTBN_ADDR_T_INIT(run_rsa_modexp, MODE_RSA_2048_MODEXP_F4);
static const uint32_t kMode3072Modexp =
    OTBN_ADDR_T_INIT(run_rsa_modexp, MODE_RSA_3072_MODEXP);
static const uint32_t kMode3072ModexpF4 =
    OTBN_ADDR_T_INIT(run_rsa_modexp, MODE_RSA_3072_MODEXP_F4);
static const uint32_t kMode4096Modexp =
    OTBN_ADDR_T_INIT(run_rsa_modexp, MODE_RSA_4096_MODEXP);
static const uint32_t kMode4096ModexpF4 =
    OTBN_ADDR_T_INIT(run_rsa_modexp, MODE_RSA_4096_MODEXP_F4);

enum {
  /**
   * Common RSA exponent with a specialized implementation.
   *
   * This exponent is 2^16 + 1, and called "F4" because it's the fourth Fermat
   * number.
   */
  kExponentF4 = 65537,
};

status_t rsa_modexp_wait(size_t *num_words) {
  // Spin here waiting for OTBN to complete.
  HARDENED_TRY(otbn_busy_wait_for_done());

  // Read the application mode.
  uint32_t mode;
  HARDENED_TRY(otbn_dmem_read(1, kOtbnVarRsaMode, &mode));

  *num_words = 0;
  if (mode == kMode2048Modexp || mode == kMode2048ModexpF4) {
    *num_words = kRsa2048NumWords;
  } else if (mode == kMode3072Modexp || mode == kMode3072ModexpF4) {
    *num_words = kRsa3072NumWords;
  } else if (mode == kMode4096Modexp || mode == kMode4096ModexpF4) {
    *num_words = kRsa4096NumWords;
  } else {
    // Unrecognized mode.
    return OTCRYPTO_FATAL_ERR;
  }

  return OTCRYPTO_OK;
}

/**
 * Finalizes a modular exponentiation of variable size.
 *
 * Blocks until OTBN is done, checks for errors. Ensures the mode matches
 * expectations. Reads back the result, and then performs an OTBN secure wipe.
 *
 * @param num_words Number of words for the modexp result.
 * @param[out] result Result of the modexp operation.
 * @return Status of the operation (OK or error).
 */
static status_t rsa_modexp_finalize(const size_t num_words, uint32_t *result) {
  // Wait for OTBN to complete and get the result size.
  size_t num_words_inferred;
  HARDENED_TRY(rsa_modexp_wait(&num_words_inferred));

  // Check that the inferred result size matches expectations.
  if (num_words != num_words_inferred) {
    return OTCRYPTO_FATAL_ERR;
  }

  // Read the result.
  HARDENED_TRY(otbn_dmem_read(num_words, kOtbnVarRsaInOut, result));

  // Wipe DMEM.
  return otbn_dmem_sec_wipe();
}

status_t rsa_modexp_consttime_2048_start(const rsa_2048_int_t *base,
                                         const rsa_2048_int_t *exp,
                                         const rsa_2048_int_t *modulus) {
  // Load the OTBN app. Fails if OTBN is not idle.
  HARDENED_TRY(otbn_load_app(kOtbnAppRsaModexp));

  // Set mode.
  uint32_t mode = kMode2048Modexp;
  HARDENED_TRY(otbn_dmem_write(1, &mode, kOtbnVarRsaMode));

  // Set the base, the modulus n and private exponent d.
  HARDENED_TRY(otbn_dmem_write(kRsa2048NumWords, base->data, kOtbnVarRsaInOut));
  HARDENED_TRY(otbn_dmem_write(kRsa2048NumWords, modulus->data, kOtbnVarRsaN));
  HARDENED_TRY(otbn_dmem_write(kRsa2048NumWords, exp->data, kOtbnVarRsaD));

  // Start OTBN.
  return otbn_execute();
}

status_t rsa_modexp_vartime_2048_start(const rsa_2048_int_t *base,
                                       const uint32_t exp,
                                       const rsa_2048_int_t *modulus) {
  if (exp != kExponentF4) {
    // TODO for other exponents, we temporarily fall back to the constant-time
    // implementation until a variable-time implementation is supported.
    rsa_2048_int_t exp_rsa;
    memset(exp_rsa.data, 0, kRsa2048NumWords * sizeof(uint32_t));
    exp_rsa.data[0] = exp;
    return rsa_modexp_consttime_2048_start(base, &exp_rsa, modulus);
  }

  // Load the OTBN app. Fails if OTBN is not idle.
  HARDENED_TRY(otbn_load_app(kOtbnAppRsaModexp));

  // Set mode.
  uint32_t mode = kMode2048ModexpF4;
  HARDENED_TRY(otbn_dmem_write(1, &mode, kOtbnVarRsaMode));

  // Set the base and the modulus n.
  HARDENED_TRY(otbn_dmem_write(kRsa2048NumWords, base->data, kOtbnVarRsaInOut));
  HARDENED_TRY(otbn_dmem_write(kRsa2048NumWords, modulus->data, kOtbnVarRsaN));

  // Start OTBN.
  return otbn_execute();
}

status_t rsa_modexp_2048_finalize(rsa_2048_int_t *result) {
  return rsa_modexp_finalize(kRsa2048NumWords, result->data);
}

status_t rsa_modexp_consttime_3072_start(const rsa_3072_int_t *base,
                                         const rsa_3072_int_t *exp,
                                         const rsa_3072_int_t *modulus) {
  // Load the OTBN app. Fails if OTBN is not idle.
  HARDENED_TRY(otbn_load_app(kOtbnAppRsaModexp));

  // Set mode.
  uint32_t mode = kMode3072Modexp;
  HARDENED_TRY(otbn_dmem_write(1, &mode, kOtbnVarRsaMode));

  // Set the base, the modulus n and private exponent d.
  HARDENED_TRY(otbn_dmem_write(kRsa3072NumWords, base->data, kOtbnVarRsaInOut));
  HARDENED_TRY(otbn_dmem_write(kRsa3072NumWords, modulus->data, kOtbnVarRsaN));
  HARDENED_TRY(otbn_dmem_write(kRsa3072NumWords, exp->data, kOtbnVarRsaD));

  // Start OTBN.
  return otbn_execute();
}

status_t rsa_modexp_vartime_3072_start(const rsa_3072_int_t *base,
                                       const uint32_t exp,
                                       const rsa_3072_int_t *modulus) {
  if (exp != kExponentF4) {
    // TODO for other exponents, we temporarily fall back to the constant-time
    // implementation until a variable-time implementation is supported.
    rsa_3072_int_t exp_rsa;
    memset(exp_rsa.data, 0, kRsa3072NumWords * sizeof(uint32_t));
    exp_rsa.data[0] = exp;
    return rsa_modexp_consttime_3072_start(base, &exp_rsa, modulus);
  }

  // Load the OTBN app. Fails if OTBN is not idle.
  HARDENED_TRY(otbn_load_app(kOtbnAppRsaModexp));

  // Set mode.
  uint32_t mode = kMode3072ModexpF4;
  HARDENED_TRY(otbn_dmem_write(1, &mode, kOtbnVarRsaMode));

  // Set the base and the modulus n.
  HARDENED_TRY(otbn_dmem_write(kRsa3072NumWords, base->data, kOtbnVarRsaInOut));
  HARDENED_TRY(otbn_dmem_write(kRsa3072NumWords, modulus->data, kOtbnVarRsaN));

  // Start OTBN.
  return otbn_execute();
}

status_t rsa_modexp_3072_finalize(rsa_3072_int_t *result) {
  return rsa_modexp_finalize(kRsa3072NumWords, result->data);
}

status_t rsa_modexp_consttime_4096_start(const rsa_4096_int_t *base,
                                         const rsa_4096_int_t *exp,
                                         const rsa_4096_int_t *modulus) {
  // Load the OTBN app. Fails if OTBN is not idle.
  HARDENED_TRY(otbn_load_app(kOtbnAppRsaModexp));

  // Set mode.
  uint32_t mode = kMode4096Modexp;
  HARDENED_TRY(otbn_dmem_write(1, &mode, kOtbnVarRsaMode));

  // Set the base, the modulus n and private exponent d.
  HARDENED_TRY(otbn_dmem_write(kRsa4096NumWords, base->data, kOtbnVarRsaInOut));
  HARDENED_TRY(otbn_dmem_write(kRsa4096NumWords, modulus->data, kOtbnVarRsaN));
  HARDENED_TRY(otbn_dmem_write(kRsa4096NumWords, exp->data, kOtbnVarRsaD));

  // Start OTBN.
  return otbn_execute();
}

status_t rsa_modexp_vartime_4096_start(const rsa_4096_int_t *base,
                                       const uint32_t exp,
                                       const rsa_4096_int_t *modulus) {
  if (exp != kExponentF4) {
    // TODO for other exponents, we temporarily fall back to the constant-time
    // implementation until a variable-time implementation is supported.
    rsa_4096_int_t exp_rsa;
    memset(exp_rsa.data, 0, kRsa4096NumWords * sizeof(uint32_t));
    exp_rsa.data[0] = exp;
    return rsa_modexp_consttime_4096_start(base, &exp_rsa, modulus);
  }

  // Load the OTBN app. Fails if OTBN is not idle.
  HARDENED_TRY(otbn_load_app(kOtbnAppRsaModexp));

  // Set mode.
  uint32_t mode = kMode4096ModexpF4;
  HARDENED_TRY(otbn_dmem_write(1, &mode, kOtbnVarRsaMode));

  // Set the base and the modulus n.
  HARDENED_TRY(otbn_dmem_write(kRsa4096NumWords, base->data, kOtbnVarRsaInOut));
  HARDENED_TRY(otbn_dmem_write(kRsa4096NumWords, modulus->data, kOtbnVarRsaN));

  // Start OTBN.
  return otbn_execute();
}

status_t rsa_modexp_4096_finalize(rsa_4096_int_t *result) {
  return rsa_modexp_finalize(kRsa4096NumWords, result->data);
}
