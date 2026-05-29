// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/impl/rsa/run_rsa.h"

#include "sw/device/lib/base/hardened_memory.h"
#include "sw/device/lib/crypto/drivers/otbn.h"

// Module ID for status codes.
#define MODULE_ID MAKE_MODULE_ID('r', 'm', 'e')

// Declare the OTBN app.
OTBN_DECLARE_APP_SYMBOLS(run_rsa);

// Declare offsets for input and output buffers.
OTBN_DECLARE_SYMBOL_ADDR(run_rsa, mode);    // Application mode.
OTBN_DECLARE_SYMBOL_ADDR(run_rsa, rsa_n);   // Public modulus n.
OTBN_DECLARE_SYMBOL_ADDR(run_rsa, rsa_d0);  // Private exponent d0.
OTBN_DECLARE_SYMBOL_ADDR(run_rsa, rsa_d1);  // Private exponent d1.
OTBN_DECLARE_SYMBOL_ADDR(run_rsa, inout);   // Input/output buffer.
OTBN_DECLARE_SYMBOL_ADDR(run_rsa, ok);      // Status of the operation.

// Miller-Rabin iteration counter for p.
OTBN_DECLARE_SYMBOL_ADDR(run_rsa, mr_iter_p);
// Miller-Rabin iteration counter for q.
OTBN_DECLARE_SYMBOL_ADDR(run_rsa, mr_iter_q);

// Declare mode constants.
OTBN_DECLARE_SYMBOL_ADDR(run_rsa, MODE_RSA_2048_KEYGEN);
OTBN_DECLARE_SYMBOL_ADDR(run_rsa, MODE_RSA_3072_KEYGEN);
OTBN_DECLARE_SYMBOL_ADDR(run_rsa, MODE_RSA_4096_KEYGEN);
OTBN_DECLARE_SYMBOL_ADDR(run_rsa, MODE_RSA_2048_MODEXP);
OTBN_DECLARE_SYMBOL_ADDR(run_rsa, MODE_RSA_2048_MODEXP_F4);
OTBN_DECLARE_SYMBOL_ADDR(run_rsa, MODE_RSA_3072_MODEXP);
OTBN_DECLARE_SYMBOL_ADDR(run_rsa, MODE_RSA_3072_MODEXP_F4);
OTBN_DECLARE_SYMBOL_ADDR(run_rsa, MODE_RSA_4096_MODEXP);
OTBN_DECLARE_SYMBOL_ADDR(run_rsa, MODE_RSA_4096_MODEXP_F4);

enum {
  /**
   * Common RSA exponent with a specialized implementation.
   *
   * This exponent is 2^16 + 1, and called "F4" because it's the fourth Fermat
   * number.
   */
  kExponentF4 = 65537,
  /**
   * Number of expected Miller-Rabin iterations.
   *
   * To have strong guarantees on the generated RSA primes, a sufficient number
   * of iterations in the Miller-Rabin primality test have to be computed.
   *
   * This value is a runtime constant in the OTBN app and is in accordance
   * with Table B.1 of FIPS 186-5.
   */
  kMrIters = 4
};

OT_NOINLINE
OT_WARN_UNUSED_RESULT
static status_t rsa_check_otbn_status(void) {
  uint32_t ok;
  const otbn_addr_t kOtbnVarOk = OTBN_ADDR_T_INIT(run_rsa, ok);

  // Read the status flag from OTBN memory
  HARDENED_TRY(otbn_dmem_read(1, kOtbnVarOk, &ok));

  // Check if it matches the expected magic value
  if (launder32(ok) != kHardenedBoolTrue) {
    HARDENED_TRY(otbn_dmem_sec_wipe());
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(ok, kHardenedBoolTrue);

  return OTCRYPTO_OK;
}

status_t rsa_modexp_wait(size_t *num_words) {
  // Spin here waiting for OTBN to complete.
  HARDENED_TRY(otbn_busy_wait_for_done());

  // Read the application mode.
  uint32_t mode;
  const otbn_addr_t kOtbnVarRsaMode = OTBN_ADDR_T_INIT(run_rsa, mode);
  HARDENED_TRY(otbn_dmem_read(1, kOtbnVarRsaMode, &mode));

  *num_words = 0;
  const uint32_t kMode2048Modexp =
      OTBN_ADDR_T_INIT(run_rsa, MODE_RSA_2048_MODEXP);
  const uint32_t kMode2048ModexpF4 =
      OTBN_ADDR_T_INIT(run_rsa, MODE_RSA_2048_MODEXP_F4);
  const uint32_t kMode3072Modexp =
      OTBN_ADDR_T_INIT(run_rsa, MODE_RSA_3072_MODEXP);
  const uint32_t kMode3072ModexpF4 =
      OTBN_ADDR_T_INIT(run_rsa, MODE_RSA_3072_MODEXP_F4);
  const uint32_t kMode4096Modexp =
      OTBN_ADDR_T_INIT(run_rsa, MODE_RSA_4096_MODEXP);
  const uint32_t kMode4096ModexpF4 =
      OTBN_ADDR_T_INIT(run_rsa, MODE_RSA_4096_MODEXP_F4);
  if (mode == kMode2048Modexp || mode == kMode2048ModexpF4) {
    *num_words = kRsa2048NumWords;
  } else if (mode == kMode3072Modexp || mode == kMode3072ModexpF4) {
    *num_words = kRsa3072NumWords;
  } else if (mode == kMode4096Modexp || mode == kMode4096ModexpF4) {
    *num_words = kRsa4096NumWords;
  } else {
    // Unrecognized mode.
    // COVERAGE (SW ERR) We only provide OTBN with correct modes.
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
    // COVERAGE (SW ERR) This is an internal functions only provided with
    // correct inputs.
    return OTCRYPTO_FATAL_ERR;
  }
  HARDENED_CHECK_EQ(launder32(num_words), num_words_inferred);

  HARDENED_TRY(rsa_check_otbn_status());

  // Read the result.
  const otbn_addr_t kOtbnVarRsaInOut = OTBN_ADDR_T_INIT(run_rsa, inout);
  HARDENED_TRY(otbn_dmem_read(num_words, kOtbnVarRsaInOut, result));

  // Wipe DMEM.
  return otbn_dmem_sec_wipe();
}

/**
 * Start the OTBN key generation program in random-key mode.
 *
 * Cofactor mode should not use this routine, because it wipes DMEM and
 * cofactor mode requires input data.
 *
 * @param mode Mode parameter for keygen.
 * @return Result of the operation.
 */
static status_t keygen_start(uint32_t mode) {
  // Load the RSA key generation app. Fails if OTBN is non-idle.
  const otbn_app_t kOtbnAppRsa = OTBN_APP_T_INIT(run_rsa);
  HARDENED_TRY(otbn_load_app(kOtbnAppRsa));

  // Set mode and start OTBN.
  const otbn_addr_t kOtbnVarRsaMode = OTBN_ADDR_T_INIT(run_rsa, mode);
  HARDENED_TRY(otbn_dmem_write(1, &mode, kOtbnVarRsaMode));

  return otbn_execute();
}

/**
 * Finalize a key generation operation (for either mode).
 *
 * Checks the application mode against expectations, then reads back the
 * modulus and private exponent.
 *
 * @param exp_mode Application mode to expect.
 * @param num_words Number of words for modulus and private exponent.
 * @param[out] n Buffer for the modulus.
 * @param[out] d0 Buffer for the private exponent share 0.
 * @param[out] d1 Buffer for the private exponent share 1.
 * @return OK or error.
 */
static status_t keygen_finalize(uint32_t exp_mode, size_t num_words,
                                uint32_t *n, uint32_t *d0, uint32_t *d1) {
  // Spin here waiting for OTBN to complete.
  HARDENED_TRY(otbn_busy_wait_for_done());

  HARDENED_TRY(rsa_check_otbn_status());

  // Read the mode from OTBN dmem and panic if it's not as expected.
  uint32_t act_mode = 0;
  uint32_t mode = OTBN_ADDR_T_INIT(run_rsa, MODE_RSA_2048_MODEXP);
  const otbn_addr_t kOtbnVarRsaMode = OTBN_ADDR_T_INIT(run_rsa, mode);
  HARDENED_TRY(otbn_dmem_read(1, kOtbnVarRsaMode, &act_mode));
  if (act_mode != exp_mode) {
    return OTCRYPTO_FATAL_ERR;
  }
  HARDENED_CHECK_EQ(launder32(act_mode), exp_mode);

  // Make sure that an exact amount of Miller-Rabin iterations have been
  // performed for both primes p and q.
  uint32_t mr_iters = 0;

  // Prime p.
  const otbn_addr_t kOtbnVarRsaMrIterP = OTBN_ADDR_T_INIT(run_rsa, mr_iter_p);
  HARDENED_TRY(otbn_dmem_read(1, kOtbnVarRsaMrIterP, &mr_iters));
  if (mr_iters != kMrIters) {
    // COVERAGE (FI CM) The number of iterations can only deviate if there was a
    // fault injection or fatal error.
    return OTCRYPTO_FATAL_ERR;
  }
  HARDENED_CHECK_EQ(launder32(mr_iters), kMrIters);

  // Prime q.
  mr_iters = 0;
  const otbn_addr_t kOtbnVarRsaMrIterQ = OTBN_ADDR_T_INIT(run_rsa, mr_iter_q);
  HARDENED_TRY(otbn_dmem_read(1, kOtbnVarRsaMrIterQ, &mr_iters));
  if (mr_iters != kMrIters) {
    // COVERAGE (FI CM) The number of iterations can only deviate if there was a
    // fault injection or fatal error.
    return OTCRYPTO_FATAL_ERR;
  }
  HARDENED_CHECK_EQ(launder32(mr_iters), kMrIters);

  // Read the public modulus (n) from OTBN dmem.
  const otbn_addr_t kOtbnVarRsaN = OTBN_ADDR_T_INIT(run_rsa, rsa_n);
  HARDENED_TRY(otbn_dmem_read(num_words, kOtbnVarRsaN, n));

  // Read the first share of the private exponent (d) from OTBN dmem.
  const otbn_addr_t kOtbnVarRsaD0 = OTBN_ADDR_T_INIT(run_rsa, rsa_d0);
  HARDENED_TRY(otbn_dmem_read(num_words, kOtbnVarRsaD0, d0));

  // Read the second share of the private exponent (d) from OTBN dmem.
  const otbn_addr_t kOtbnVarRsaD1 = OTBN_ADDR_T_INIT(run_rsa, rsa_d1);
  HARDENED_TRY(otbn_dmem_read(num_words, kOtbnVarRsaD1, d1));

  // Wipe DMEM.
  return otbn_dmem_sec_wipe();
}

status_t rsa_modexp_consttime_start(rsa_size_t size, const uint32_t *base,
                                    const uint32_t *exp0, const uint32_t *exp1,
                                    const uint32_t *modulus) {
  // Load the OTBN app. Fails if OTBN is not idle.
  const otbn_app_t kOtbnAppRsa = OTBN_APP_T_INIT(run_rsa);
  HARDENED_TRY(otbn_load_app(kOtbnAppRsa));

  size_t num_words = 0;
  uint32_t mode = 0;

  switch (launder32(size)) {
    case kRsaSize2048:
      HARDENED_CHECK_EQ(size, kRsaSize2048);
      num_words = kRsa2048NumWords;
      const uint32_t kMode2048Modexp =
          OTBN_ADDR_T_INIT(run_rsa, MODE_RSA_2048_MODEXP);
      mode = kMode2048Modexp;
      break;
    case kRsaSize3072:
      HARDENED_CHECK_EQ(size, kRsaSize3072);
      num_words = kRsa3072NumWords;
      const uint32_t kMode3072Modexp =
          OTBN_ADDR_T_INIT(run_rsa, MODE_RSA_3072_MODEXP);
      mode = kMode3072Modexp;
      break;
    case kRsaSize4096:
      HARDENED_CHECK_EQ(size, kRsaSize4096);
      num_words = kRsa4096NumWords;
      const uint32_t kMode4096Modexp =
          OTBN_ADDR_T_INIT(run_rsa, MODE_RSA_4096_MODEXP);
      mode = kMode4096Modexp;
      break;
    default:
      HARDENED_TRAP();
      // COVERAGE (FI CM) Unreachable code, checked against fault injections.
      return OTCRYPTO_FATAL_ERR;
  }

  // Set mode.
  const otbn_addr_t kOtbnVarRsaMode = OTBN_ADDR_T_INIT(run_rsa, mode);
  HARDENED_TRY(otbn_dmem_write(1, &mode, kOtbnVarRsaMode));

  // Set the base, the modulus n and private exponent d.
  const otbn_addr_t kOtbnVarRsaInOut = OTBN_ADDR_T_INIT(run_rsa, inout);
  HARDENED_TRY(otbn_dmem_write(num_words, base, kOtbnVarRsaInOut));
  const otbn_addr_t kOtbnVarRsaN = OTBN_ADDR_T_INIT(run_rsa, rsa_n);
  HARDENED_TRY(otbn_dmem_write(num_words, modulus, kOtbnVarRsaN));
  const otbn_addr_t kOtbnVarRsaD0 = OTBN_ADDR_T_INIT(run_rsa, rsa_d0);
  HARDENED_TRY(otbn_dmem_write(num_words, exp0, kOtbnVarRsaD0));
  const otbn_addr_t kOtbnVarRsaD1 = OTBN_ADDR_T_INIT(run_rsa, rsa_d1);
  HARDENED_TRY(otbn_dmem_write(num_words, exp1, kOtbnVarRsaD1));

  // Start OTBN.
  return otbn_execute();
}

status_t rsa_modexp_vartime_start(rsa_size_t size, const uint32_t *base,
                                  const uint32_t *modulus) {
  // Load the OTBN app. Fails if OTBN is not idle.
  const otbn_app_t kOtbnAppRsa = OTBN_APP_T_INIT(run_rsa);
  HARDENED_TRY(otbn_load_app(kOtbnAppRsa));

  size_t num_words = 0;
  uint32_t mode = 0;

  switch (launder32(size)) {
    case kRsaSize2048:
      HARDENED_CHECK_EQ(size, kRsaSize2048);
      num_words = kRsa2048NumWords;
      const uint32_t kMode2048ModexpF4 =
          OTBN_ADDR_T_INIT(run_rsa, MODE_RSA_2048_MODEXP_F4);
      mode = kMode2048ModexpF4;
      break;
    case kRsaSize3072:
      HARDENED_CHECK_EQ(size, kRsaSize3072);
      num_words = kRsa3072NumWords;
      const uint32_t kMode3072ModexpF4 =
          OTBN_ADDR_T_INIT(run_rsa, MODE_RSA_3072_MODEXP_F4);
      mode = kMode3072ModexpF4;
      break;
    case kRsaSize4096:
      HARDENED_CHECK_EQ(size, kRsaSize4096);
      num_words = kRsa4096NumWords;
      const uint32_t kMode4096ModexpF4 =
          OTBN_ADDR_T_INIT(run_rsa, MODE_RSA_4096_MODEXP_F4);
      mode = kMode4096ModexpF4;
      break;
    default:
      HARDENED_TRAP();
      // COVERAGE (FI CM) Unreachable code, checked against fault injections.
      return OTCRYPTO_FATAL_ERR;
  }

  // Set mode.
  const otbn_addr_t kOtbnVarRsaMode = OTBN_ADDR_T_INIT(run_rsa, mode);
  HARDENED_TRY(otbn_dmem_write(1, &mode, kOtbnVarRsaMode));

  // Set the base and the modulus n.
  const otbn_addr_t kOtbnVarRsaInOut = OTBN_ADDR_T_INIT(run_rsa, inout);
  HARDENED_TRY(otbn_dmem_write(num_words, base, kOtbnVarRsaInOut));
  const otbn_addr_t kOtbnVarRsaN = OTBN_ADDR_T_INIT(run_rsa, rsa_n);
  HARDENED_TRY(otbn_dmem_write(num_words, modulus, kOtbnVarRsaN));

  // Start OTBN.
  return otbn_execute();
}

status_t rsa_modexp_finalize_size(rsa_size_t size, uint32_t *result) {
  size_t expected_words = 0;
  switch (launder32(size)) {
    case kRsaSize2048:
      HARDENED_CHECK_EQ(size, kRsaSize2048);
      expected_words = kRsa2048NumWords;
      break;
    case kRsaSize3072:
      HARDENED_CHECK_EQ(size, kRsaSize3072);
      expected_words = kRsa3072NumWords;
      break;
    case kRsaSize4096:
      HARDENED_CHECK_EQ(size, kRsaSize4096);
      expected_words = kRsa4096NumWords;
      break;
    default:
      HARDENED_TRAP();
      // COVERAGE (FI CM) Unreachable code, checked against fault injections.
      return OTCRYPTO_FATAL_ERR;
  }
  return rsa_modexp_finalize(expected_words, result);
}

status_t rsa_keygen_start(rsa_size_t size) {
  uint32_t mode = 0;
  switch (launder32(size)) {
    case kRsaSize2048:
      HARDENED_CHECK_EQ(size, kRsaSize2048);
      const uint32_t kMode2048Keygen =
          OTBN_ADDR_T_INIT(run_rsa, MODE_RSA_2048_KEYGEN);
      mode = kMode2048Keygen;
      break;
    case kRsaSize3072:
      HARDENED_CHECK_EQ(size, kRsaSize3072);
      const uint32_t kMode3072Keygen =
          OTBN_ADDR_T_INIT(run_rsa, MODE_RSA_3072_KEYGEN);
      mode = kMode3072Keygen;
      break;
    case kRsaSize4096:
      HARDENED_CHECK_EQ(size, kRsaSize4096);
      const uint32_t kMode4096Keygen =
          OTBN_ADDR_T_INIT(run_rsa, MODE_RSA_4096_KEYGEN);
      mode = kMode4096Keygen;
      break;
    default:
      HARDENED_TRAP();
      // COVERAGE (FI CM) Unreachable code, checked against fault injections.
      return OTCRYPTO_FATAL_ERR;
  }
  return keygen_start(mode);
}

status_t rsa_keygen_finalize_size(rsa_size_t size, uint32_t *n, uint32_t *d0,
                                  uint32_t *d1) {
  uint32_t mode = 0;
  size_t expected_words = 0;

  switch (launder32(size)) {
    case kRsaSize2048:
      HARDENED_CHECK_EQ(size, kRsaSize2048);
      const uint32_t kMode2048Keygen =
          OTBN_ADDR_T_INIT(run_rsa, MODE_RSA_2048_KEYGEN);
      mode = kMode2048Keygen;
      expected_words = kRsa2048NumWords;
      break;
    case kRsaSize3072:
      HARDENED_CHECK_EQ(size, kRsaSize3072);
      const uint32_t kMode3072Keygen =
          OTBN_ADDR_T_INIT(run_rsa, MODE_RSA_3072_KEYGEN);
      mode = kMode3072Keygen;
      expected_words = kRsa3072NumWords;
      break;
    case kRsaSize4096:
      HARDENED_CHECK_EQ(size, kRsaSize4096);
      const uint32_t kMode4096Keygen =
          OTBN_ADDR_T_INIT(run_rsa, MODE_RSA_4096_KEYGEN);
      mode = kMode4096Keygen;
      expected_words = kRsa4096NumWords;
      break;
    default:
      HARDENED_TRAP();
      // COVERAGE (FI CM) Unreachable code, checked against fault injections.
      return OTCRYPTO_FATAL_ERR;
  }

  return keygen_finalize(mode, expected_words, n, d0, d1);
}
