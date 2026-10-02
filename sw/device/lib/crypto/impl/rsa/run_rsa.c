// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/impl/rsa/run_rsa.h"

#include "sw/device/lib/base/crc32.h"
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
OTBN_DECLARE_SYMBOL_ADDR(run_rsa, rsa_e);   // Custom public exponent e.

// Miller-Rabin iteration counter for p.
OTBN_DECLARE_SYMBOL_ADDR(run_rsa, mr_iter_p);
// Miller-Rabin iteration counter for q.
OTBN_DECLARE_SYMBOL_ADDR(run_rsa, mr_iter_q);

// RSA primes, testing only.
OTBN_DECLARE_SYMBOL_ADDR(run_rsa, rsa_p);
OTBN_DECLARE_SYMBOL_ADDR(run_rsa, rsa_q);

// Declare mode constants.
OTBN_DECLARE_SYMBOL_ADDR(run_rsa, MODE_RSA_2048_KEYGEN);
OTBN_DECLARE_SYMBOL_ADDR(run_rsa, MODE_RSA_3072_KEYGEN);
OTBN_DECLARE_SYMBOL_ADDR(run_rsa, MODE_RSA_4096_KEYGEN);
OTBN_DECLARE_SYMBOL_ADDR(run_rsa, MODE_RSA_2048_MODEXP);
OTBN_DECLARE_SYMBOL_ADDR(run_rsa, MODE_RSA_2048_MODEXP_F4);
OTBN_DECLARE_SYMBOL_ADDR(run_rsa, MODE_RSA_2048_MODEXP_DE);
OTBN_DECLARE_SYMBOL_ADDR(run_rsa, MODE_RSA_2048_MODEXP_E);
OTBN_DECLARE_SYMBOL_ADDR(run_rsa, MODE_RSA_3072_MODEXP);
OTBN_DECLARE_SYMBOL_ADDR(run_rsa, MODE_RSA_3072_MODEXP_F4);
OTBN_DECLARE_SYMBOL_ADDR(run_rsa, MODE_RSA_3072_MODEXP_DE);
OTBN_DECLARE_SYMBOL_ADDR(run_rsa, MODE_RSA_3072_MODEXP_E);
OTBN_DECLARE_SYMBOL_ADDR(run_rsa, MODE_RSA_4096_MODEXP);
OTBN_DECLARE_SYMBOL_ADDR(run_rsa, MODE_RSA_4096_MODEXP_F4);
OTBN_DECLARE_SYMBOL_ADDR(run_rsa, MODE_RSA_4096_MODEXP_DE);
OTBN_DECLARE_SYMBOL_ADDR(run_rsa, MODE_RSA_4096_MODEXP_E);

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
  kMrIters = 4,
  /**
   * Expected instruction counts for constant-time modexp operations.
   */
  kModeRsa2048ModexpInsCnt = 16302885,
  kModeRsa2048ModexpF4InsCnt = 108418,
  kModeRsa2048ModexpDEInsCnt = 16485117,
  kModeRsa2048ModexpEInsCnt = 279316,
  kModeRsa3072ModexpInsCnt = 52084284,
  kModeRsa3072ModexpF4InsCnt = 230702,
  kModeRsa3072ModexpDEInsCnt = 52479320,
  kModeRsa3072ModexpEInsCnt = 601116,
  kModeRsa4096ModexpInsCnt = 120180626,
  kModeRsa4096ModexpF4InsCnt = 399642,
  kModeRsa4096ModexpDEInsCnt = 120869873,
  kModeRsa4096ModexpEInsCnt = 1045892,
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
    // COVERAGE (FI CM) This check only fails if OTBN execution was faulted or
    // given invalid inputs.
    HARDENED_TRY(otbn_dmem_sec_wipe());
    return OTCRYPTO_RECOV_ERR;
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
  uint32_t exp_insn_cnt = 0;
  const uint32_t kMode2048Modexp =
      OTBN_ADDR_T_INIT(run_rsa, MODE_RSA_2048_MODEXP);
  const uint32_t kMode2048ModexpF4 =
      OTBN_ADDR_T_INIT(run_rsa, MODE_RSA_2048_MODEXP_F4);
  const uint32_t kMode2048ModexpDE =
      OTBN_ADDR_T_INIT(run_rsa, MODE_RSA_2048_MODEXP_DE);
  const uint32_t kMode2048ModexpE =
      OTBN_ADDR_T_INIT(run_rsa, MODE_RSA_2048_MODEXP_E);
  const uint32_t kMode3072Modexp =
      OTBN_ADDR_T_INIT(run_rsa, MODE_RSA_3072_MODEXP);
  const uint32_t kMode3072ModexpF4 =
      OTBN_ADDR_T_INIT(run_rsa, MODE_RSA_3072_MODEXP_F4);
  const uint32_t kMode3072ModexpDE =
      OTBN_ADDR_T_INIT(run_rsa, MODE_RSA_3072_MODEXP_DE);
  const uint32_t kMode3072ModexpE =
      OTBN_ADDR_T_INIT(run_rsa, MODE_RSA_3072_MODEXP_E);
  const uint32_t kMode4096Modexp =
      OTBN_ADDR_T_INIT(run_rsa, MODE_RSA_4096_MODEXP);
  const uint32_t kMode4096ModexpF4 =
      OTBN_ADDR_T_INIT(run_rsa, MODE_RSA_4096_MODEXP_F4);
  const uint32_t kMode4096ModexpDE =
      OTBN_ADDR_T_INIT(run_rsa, MODE_RSA_4096_MODEXP_DE);
  const uint32_t kMode4096ModexpE =
      OTBN_ADDR_T_INIT(run_rsa, MODE_RSA_4096_MODEXP_E);
  if (mode == kMode2048Modexp || mode == kMode2048ModexpF4 ||
      mode == kMode2048ModexpDE || mode == kMode2048ModexpE) {
    *num_words = kRsa2048NumWords;
    exp_insn_cnt = (mode == kMode2048Modexp)     ? kModeRsa2048ModexpInsCnt
                   : (mode == kMode2048ModexpF4) ? kModeRsa2048ModexpF4InsCnt
                   : (mode == kMode2048ModexpDE) ? kModeRsa2048ModexpDEInsCnt
                                                 : kModeRsa2048ModexpEInsCnt;
  } else if (mode == kMode3072Modexp || mode == kMode3072ModexpF4 ||
             mode == kMode3072ModexpDE || mode == kMode3072ModexpE) {
    *num_words = kRsa3072NumWords;
    exp_insn_cnt = (mode == kMode3072Modexp)     ? kModeRsa3072ModexpInsCnt
                   : (mode == kMode3072ModexpF4) ? kModeRsa3072ModexpF4InsCnt
                   : (mode == kMode3072ModexpDE)
                       ? kModeRsa3072ModexpDEInsCnt
                       // COVERAGE (MISSING) We do not cover custom public
                       // exponents for RSA-3072.
                       : kModeRsa3072ModexpEInsCnt;
  } else if (mode == kMode4096Modexp || mode == kMode4096ModexpF4 ||
             mode == kMode4096ModexpDE || mode == kMode4096ModexpE) {
    *num_words = kRsa4096NumWords;
    exp_insn_cnt = (mode == kMode4096Modexp)     ? kModeRsa4096ModexpInsCnt
                   : (mode == kMode4096ModexpF4) ? kModeRsa4096ModexpF4InsCnt
                   : (mode == kMode4096ModexpDE)
                       ? kModeRsa4096ModexpDEInsCnt
                       // COVERAGE (MISSING) We do not cover custom public
                       // exponents for RSA-4096.
                       : kModeRsa4096ModexpEInsCnt;
  } else {
    // Unrecognized mode.
    return OTCRYPTO_FATAL_ERR;
  }
  HARDENED_CHECK_EQ(otbn_instruction_count_get(), exp_insn_cnt);

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
  if (launder32(num_words) != num_words_inferred) {
    return OTCRYPTO_FATAL_ERR;
  }
  HARDENED_CHECK_EQ(num_words, num_words_inferred);

  HARDENED_TRY(rsa_check_otbn_status());

  // Read the result.
  const otbn_addr_t kOtbnVarRsaInOut = OTBN_ADDR_T_INIT(run_rsa, inout);
  HARDENED_TRY(otbn_dmem_read(num_words, kOtbnVarRsaInOut, result));

  // The output result should not be zero
  size_t i = 0;
  uint32_t result_bits_or = 0;
  for (; launder32(i) < num_words; ++i) {
    result_bits_or |= result[i];
  }
  HARDENED_CHECK_EQ(i, num_words);
  if (launder32(result_bits_or) == 0) {
    HARDENED_TRY(otbn_dmem_sec_wipe());
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_NE(result_bits_or, 0);

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
  HARDENED_TRY(otbn_dmem_write_public(1, &mode, kOtbnVarRsaMode));

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
 * @param[out] p Buffer for the prime p, optionally read out if not null.
 * @param[out] q Buffer for the prime q, optionally read out if not null.
 * @return OK or error.
 */
static status_t keygen_finalize(uint32_t exp_mode, size_t num_words,
                                uint32_t *n, uint32_t *d0, uint32_t *d1,
                                uint32_t *p, uint32_t *q) {
  // Spin here waiting for OTBN to complete.
  HARDENED_TRY(otbn_busy_wait_for_done());

  HARDENED_TRY(rsa_check_otbn_status());

  // Read the mode from OTBN dmem and panic if it's not as expected.
  uint32_t act_mode = 0;
  const otbn_addr_t kOtbnVarRsaMode = OTBN_ADDR_T_INIT(run_rsa, mode);
  HARDENED_TRY(otbn_dmem_read(1, kOtbnVarRsaMode, &act_mode));
  if (launder32(act_mode) != exp_mode) {
    return OTCRYPTO_RECOV_ERR;
  }
  HARDENED_CHECK_EQ(act_mode, exp_mode);

  // Make sure that an exact amount of Miller-Rabin iterations have been
  // performed for both primes p and q.
  uint32_t mr_iters = 0;

  // Prime p.
  const otbn_addr_t kOtbnVarRsaMrIterP = OTBN_ADDR_T_INIT(run_rsa, mr_iter_p);
  HARDENED_TRY(otbn_dmem_read(1, kOtbnVarRsaMrIterP, &mr_iters));
  if (launder32(mr_iters) != kMrIters) {
    return OTCRYPTO_FATAL_ERR;
  }
  HARDENED_CHECK_EQ(mr_iters, kMrIters);

  // Prime q.
  mr_iters = 0;
  const otbn_addr_t kOtbnVarRsaMrIterQ = OTBN_ADDR_T_INIT(run_rsa, mr_iter_q);
  HARDENED_TRY(otbn_dmem_read(1, kOtbnVarRsaMrIterQ, &mr_iters));
  if (launder32(mr_iters) != kMrIters) {
    return OTCRYPTO_FATAL_ERR;
  }
  HARDENED_CHECK_EQ(mr_iters, kMrIters);

  // Read the public modulus (n) from OTBN dmem.
  const otbn_addr_t kOtbnVarRsaN = OTBN_ADDR_T_INIT(run_rsa, rsa_n);
  HARDENED_TRY(otbn_dmem_read(num_words, kOtbnVarRsaN, n));

  // Read the first share of the private exponent (d) from OTBN dmem.
  const otbn_addr_t kOtbnVarRsaD0 = OTBN_ADDR_T_INIT(run_rsa, rsa_d0);
  HARDENED_TRY(otbn_dmem_read(num_words, kOtbnVarRsaD0, d0));

  // Read the second share of the private exponent (d) from OTBN dmem.
  const otbn_addr_t kOtbnVarRsaD1 = OTBN_ADDR_T_INIT(run_rsa, rsa_d1);
  HARDENED_TRY(otbn_dmem_read(num_words, kOtbnVarRsaD1, d1));

  // Optionally read out the primes p and q.
  if (p != NULL) {
    // COVERAGE (SW ERR) Testing-only prime readout is not used by standard
    // keygen callers.
    const otbn_addr_t kOtbnVarRsaP = OTBN_ADDR_T_INIT(run_rsa, rsa_p);
    HARDENED_TRY(otbn_dmem_read(num_words >> 1, kOtbnVarRsaP, p));
  }
  if (q != NULL) {
    // COVERAGE (SW ERR) Testing-only prime readout is not used by standard
    // keygen callers.
    const otbn_addr_t kOtbnVarRsaQ = OTBN_ADDR_T_INIT(run_rsa, rsa_q);
    HARDENED_TRY(otbn_dmem_read(num_words >> 1, kOtbnVarRsaQ, q));
  }

  // Wipe DMEM.
  return otbn_dmem_sec_wipe();
}

status_t rsa_modexp_consttime_start(rsa_size_t size, const uint32_t *base,
                                    const uint32_t *exp0, const uint32_t *exp1,
                                    uint32_t pub_exp, const uint32_t *modulus,
                                    uint32_t checksum) {
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
      const uint32_t kMode2048ModexpDE =
          OTBN_ADDR_T_INIT(run_rsa, MODE_RSA_2048_MODEXP_DE);
      mode = (pub_exp == 0) ? kMode2048Modexp : kMode2048ModexpDE;
      break;
    case kRsaSize3072:
      HARDENED_CHECK_EQ(size, kRsaSize3072);
      num_words = kRsa3072NumWords;
      const uint32_t kMode3072Modexp =
          OTBN_ADDR_T_INIT(run_rsa, MODE_RSA_3072_MODEXP);
      const uint32_t kMode3072ModexpDE =
          OTBN_ADDR_T_INIT(run_rsa, MODE_RSA_3072_MODEXP_DE);
      mode = (pub_exp == 0) ? kMode3072Modexp : kMode3072ModexpDE;
      break;
    case kRsaSize4096:
      HARDENED_CHECK_EQ(size, kRsaSize4096);
      num_words = kRsa4096NumWords;
      const uint32_t kMode4096Modexp =
          OTBN_ADDR_T_INIT(run_rsa, MODE_RSA_4096_MODEXP);
      const uint32_t kMode4096ModexpDE =
          OTBN_ADDR_T_INIT(run_rsa, MODE_RSA_4096_MODEXP_DE);
      mode = (pub_exp == 0) ? kMode4096Modexp : kMode4096ModexpDE;
      break;
    default:
      HARDENED_TRAP();
      return OTCRYPTO_FATAL_ERR;
  }

  // Verify the checksum over share 0 (exp0).
  if (checksum != launder32(crc32(exp0, num_words * sizeof(uint32_t)))) {
    // COVERAGE (FI CM) The outer blinded key checksum is already verified, so
    // the inner share checksum only fails under fault injection or memory
    // corruption.
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(checksum, crc32(exp0, num_words * sizeof(uint32_t)));

  // Set mode and (if using a custom exponent) public exponent e.
  const otbn_addr_t kOtbnVarRsaMode = OTBN_ADDR_T_INIT(run_rsa, mode);
  HARDENED_TRY(otbn_dmem_write_public(1, &mode, kOtbnVarRsaMode));
  if (pub_exp != 0) {
    const otbn_addr_t kOtbnVarRsaE = OTBN_ADDR_T_INIT(run_rsa, rsa_e);
    HARDENED_TRY(otbn_dmem_write_public(1, &pub_exp, kOtbnVarRsaE));
  }

  // Set the base, the modulus n and private exponent d.
  const otbn_addr_t kOtbnVarRsaInOut = OTBN_ADDR_T_INIT(run_rsa, inout);
  HARDENED_TRY(otbn_dmem_write_public(num_words, base, kOtbnVarRsaInOut));
  const otbn_addr_t kOtbnVarRsaN = OTBN_ADDR_T_INIT(run_rsa, rsa_n);
  HARDENED_TRY(otbn_dmem_write_public(num_words, modulus, kOtbnVarRsaN));
  const otbn_addr_t kOtbnVarRsaD0 = OTBN_ADDR_T_INIT(run_rsa, rsa_d0);
  HARDENED_TRY(otbn_dmem_write(num_words, exp0, kOtbnVarRsaD0));
  const otbn_addr_t kOtbnVarRsaD1 = OTBN_ADDR_T_INIT(run_rsa, rsa_d1);
  HARDENED_TRY(otbn_dmem_write(num_words, exp1, kOtbnVarRsaD1));

  // Start OTBN.
  return otbn_execute();
}

status_t rsa_modexp_vartime_start(rsa_size_t size, const uint32_t *base,
                                  uint32_t exp, const uint32_t *modulus) {
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
      const uint32_t kMode2048ModexpE =
          OTBN_ADDR_T_INIT(run_rsa, MODE_RSA_2048_MODEXP_E);
      mode = (exp == 0) ? kMode2048ModexpF4 : kMode2048ModexpE;
      break;
    case kRsaSize3072:
      HARDENED_CHECK_EQ(size, kRsaSize3072);
      num_words = kRsa3072NumWords;
      const uint32_t kMode3072ModexpF4 =
          OTBN_ADDR_T_INIT(run_rsa, MODE_RSA_3072_MODEXP_F4);
      const uint32_t kMode3072ModexpE =
          OTBN_ADDR_T_INIT(run_rsa, MODE_RSA_3072_MODEXP_E);
      mode = (exp == 0) ? kMode3072ModexpF4 : kMode3072ModexpE;
      break;
    case kRsaSize4096:
      HARDENED_CHECK_EQ(size, kRsaSize4096);
      num_words = kRsa4096NumWords;
      const uint32_t kMode4096ModexpF4 =
          OTBN_ADDR_T_INIT(run_rsa, MODE_RSA_4096_MODEXP_F4);
      const uint32_t kMode4096ModexpE =
          OTBN_ADDR_T_INIT(run_rsa, MODE_RSA_4096_MODEXP_E);
      mode = (exp == 0) ? kMode4096ModexpF4 : kMode4096ModexpE;
      break;
    default:
      HARDENED_TRAP();
      return OTCRYPTO_FATAL_ERR;
  }

  // Set mode and (if using a custom exponent) public exponent e.
  const otbn_addr_t kOtbnVarRsaMode = OTBN_ADDR_T_INIT(run_rsa, mode);
  HARDENED_TRY(otbn_dmem_write_public(1, &mode, kOtbnVarRsaMode));
  if (exp != 0) {
    const otbn_addr_t kOtbnVarRsaE = OTBN_ADDR_T_INIT(run_rsa, rsa_e);
    HARDENED_TRY(otbn_dmem_write_public(1, &exp, kOtbnVarRsaE));
  }

  // Set the base and the modulus n.
  const otbn_addr_t kOtbnVarRsaInOut = OTBN_ADDR_T_INIT(run_rsa, inout);
  HARDENED_TRY(otbn_dmem_write_public(num_words, base, kOtbnVarRsaInOut));
  const otbn_addr_t kOtbnVarRsaN = OTBN_ADDR_T_INIT(run_rsa, rsa_n);
  HARDENED_TRY(otbn_dmem_write_public(num_words, modulus, kOtbnVarRsaN));

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
      return OTCRYPTO_FATAL_ERR;
  }
  return keygen_start(mode);
}

status_t rsa_keygen_finalize_size(rsa_size_t size, uint32_t *n, uint32_t *d0,
                                  uint32_t *d1, uint32_t *p, uint32_t *q) {
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
      return OTCRYPTO_FATAL_ERR;
  }

  return keygen_finalize(mode, expected_words, n, d0, d1, p, q);
}
