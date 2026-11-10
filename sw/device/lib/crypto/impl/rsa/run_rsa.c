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
OTBN_DECLARE_SYMBOL_ADDR(run_rsa, MODE_RSA_2048_CHECK_N);
OTBN_DECLARE_SYMBOL_ADDR(run_rsa, MODE_RSA_3072_CHECK_N);
OTBN_DECLARE_SYMBOL_ADDR(run_rsa, MODE_RSA_4096_CHECK_N);

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

typedef struct rsa_otbn_modes {
  size_t num_words;
  uint32_t keygen;
  uint32_t check_n;
  uint32_t modexp;
  uint32_t modexp_f4;
  uint32_t modexp_de;
  uint32_t modexp_e;
  uint32_t insn_modexp;
  uint32_t insn_modexp_f4;
  uint32_t insn_modexp_de;
  uint32_t insn_modexp_e;
} rsa_otbn_modes_t;

OT_NOINLINE
OT_WARN_UNUSED_RESULT
static status_t rsa_get_otbn_modes(rsa_size_t size, rsa_otbn_modes_t *modes) {
  switch (launder32(size)) {
    case kRsaSize2048:
      HARDENED_CHECK_EQ(size, kRsaSize2048);
      *modes = (rsa_otbn_modes_t){
          .num_words = kRsa2048NumWords,
          .keygen = OTBN_ADDR_T_INIT(run_rsa, MODE_RSA_2048_KEYGEN),
          .check_n = OTBN_ADDR_T_INIT(run_rsa, MODE_RSA_2048_CHECK_N),
          .modexp = OTBN_ADDR_T_INIT(run_rsa, MODE_RSA_2048_MODEXP),
          .modexp_f4 = OTBN_ADDR_T_INIT(run_rsa, MODE_RSA_2048_MODEXP_F4),
          .modexp_de = OTBN_ADDR_T_INIT(run_rsa, MODE_RSA_2048_MODEXP_DE),
          .modexp_e = OTBN_ADDR_T_INIT(run_rsa, MODE_RSA_2048_MODEXP_E),
          .insn_modexp = kModeRsa2048ModexpInsCnt,
          .insn_modexp_f4 = kModeRsa2048ModexpF4InsCnt,
          .insn_modexp_de = kModeRsa2048ModexpDEInsCnt,
          .insn_modexp_e = kModeRsa2048ModexpEInsCnt,
      };
      return OTCRYPTO_OK;
    case kRsaSize3072:
      HARDENED_CHECK_EQ(size, kRsaSize3072);
      *modes = (rsa_otbn_modes_t){
          .num_words = kRsa3072NumWords,
          .keygen = OTBN_ADDR_T_INIT(run_rsa, MODE_RSA_3072_KEYGEN),
          .check_n = OTBN_ADDR_T_INIT(run_rsa, MODE_RSA_3072_CHECK_N),
          .modexp = OTBN_ADDR_T_INIT(run_rsa, MODE_RSA_3072_MODEXP),
          .modexp_f4 = OTBN_ADDR_T_INIT(run_rsa, MODE_RSA_3072_MODEXP_F4),
          .modexp_de = OTBN_ADDR_T_INIT(run_rsa, MODE_RSA_3072_MODEXP_DE),
          .modexp_e = OTBN_ADDR_T_INIT(run_rsa, MODE_RSA_3072_MODEXP_E),
          .insn_modexp = kModeRsa3072ModexpInsCnt,
          .insn_modexp_f4 = kModeRsa3072ModexpF4InsCnt,
          .insn_modexp_de = kModeRsa3072ModexpDEInsCnt,
          .insn_modexp_e = kModeRsa3072ModexpEInsCnt,
      };
      return OTCRYPTO_OK;
    case kRsaSize4096:
      HARDENED_CHECK_EQ(size, kRsaSize4096);
      *modes = (rsa_otbn_modes_t){
          .num_words = kRsa4096NumWords,
          .keygen = OTBN_ADDR_T_INIT(run_rsa, MODE_RSA_4096_KEYGEN),
          .check_n = OTBN_ADDR_T_INIT(run_rsa, MODE_RSA_4096_CHECK_N),
          .modexp = OTBN_ADDR_T_INIT(run_rsa, MODE_RSA_4096_MODEXP),
          .modexp_f4 = OTBN_ADDR_T_INIT(run_rsa, MODE_RSA_4096_MODEXP_F4),
          .modexp_de = OTBN_ADDR_T_INIT(run_rsa, MODE_RSA_4096_MODEXP_DE),
          .modexp_e = OTBN_ADDR_T_INIT(run_rsa, MODE_RSA_4096_MODEXP_E),
          .insn_modexp = kModeRsa4096ModexpInsCnt,
          .insn_modexp_f4 = kModeRsa4096ModexpF4InsCnt,
          .insn_modexp_de = kModeRsa4096ModexpDEInsCnt,
          .insn_modexp_e = kModeRsa4096ModexpEInsCnt,
      };
      return OTCRYPTO_OK;
    default:
      HARDENED_TRAP();
      // COVERAGE (FI CM) Unreachable code, checked against fault injections.
      return OTCRYPTO_FATAL_ERR;
  }
}

OT_NOINLINE
OT_WARN_UNUSED_RESULT
static status_t rsa_init_otbn(uint32_t mode) {
  HARDENED_TRY(otbn_load_app(OTBN_APP_T_INIT(run_rsa)));
  return otbn_dmem_write(1, &mode, OTBN_ADDR_T_INIT(run_rsa, mode));
}

OT_NOINLINE
OT_WARN_UNUSED_RESULT
static status_t rsa_check_mode(uint32_t exp_mode) {
  uint32_t act_mode = 0;
  HARDENED_TRY(otbn_dmem_read(1, OTBN_ADDR_T_INIT(run_rsa, mode), &act_mode));
  if (launder32(act_mode) != exp_mode) {
    return OTCRYPTO_RECOV_ERR;
  }
  HARDENED_CHECK_EQ(act_mode, exp_mode);
  return OTCRYPTO_OK;
}

OT_NOINLINE
OT_WARN_UNUSED_RESULT
static status_t rsa_check_mr_iters(otbn_addr_t addr) {
  uint32_t mr_iters = 0;
  HARDENED_TRY(otbn_dmem_read(1, addr, &mr_iters));
  if (launder32(mr_iters) != kMrIters) {
    return OTCRYPTO_FATAL_ERR;
  }
  HARDENED_CHECK_EQ(mr_iters, kMrIters);
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
  static const rsa_size_t kRsaSizes[3] = {
      kRsaSize2048,
      kRsaSize3072,
      kRsaSize4096,
  };
  for (size_t i = 0; i < ARRAYSIZE(kRsaSizes); ++i) {
    rsa_otbn_modes_t m;
    HARDENED_TRY(rsa_get_otbn_modes(kRsaSizes[i], &m));
    if (mode == m.modexp || mode == m.modexp_f4 || mode == m.modexp_de ||
        mode == m.modexp_e) {
      *num_words = m.num_words;
      uint32_t exp_insn_cnt = (mode == m.modexp)      ? m.insn_modexp
                              : (mode == m.modexp_f4) ? m.insn_modexp_f4
                              : (mode == m.modexp_de) ? m.insn_modexp_de
                                                      : m.insn_modexp_e;
      HARDENED_CHECK_EQ(otbn_instruction_count_get(), exp_insn_cnt);
      return OTCRYPTO_OK;
    }
  }

  // Unrecognized mode.
  // COVERAGE (SW ERR) We only provide OTBN with correct modes.
  return OTCRYPTO_FATAL_ERR;
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
status_t rsa_modexp_finalize(const size_t num_words, uint32_t *result) {
  // Wait for OTBN to complete and get the result size.
  size_t num_words_inferred;
  HARDENED_TRY(rsa_modexp_wait(&num_words_inferred));

  // Check that the inferred result size matches expectations.
  if (launder32(num_words) != num_words_inferred) {
    // COVERAGE (SW ERR) This is an internal functions only provided with
    // correct inputs.
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
  HARDENED_TRY(rsa_init_otbn(mode));

  // Ensure deterministic keygen mode is disabled.
  uint32_t det = kHardenedBoolFalse;
  HARDENED_TRY(otbn_dmem_write(1, &det, OTBN_ADDR_T_INIT(run_rsa, rsa_e)));

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
  HARDENED_TRY(rsa_check_mode(exp_mode));
  HARDENED_TRY(rsa_check_mr_iters(OTBN_ADDR_T_INIT(run_rsa, mr_iter_p)));
  HARDENED_TRY(rsa_check_mr_iters(OTBN_ADDR_T_INIT(run_rsa, mr_iter_q)));

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
  rsa_otbn_modes_t m;
  HARDENED_TRY(rsa_get_otbn_modes(size, &m));
  size_t num_words = m.num_words;
  uint32_t mode = (pub_exp == 0) ? m.modexp : m.modexp_de;

  // Verify the checksum over share 0 (exp0).
  if (checksum != launder32(crc32(exp0, num_words * sizeof(uint32_t)))) {
    // COVERAGE (FI CM) The outer blinded key checksum is already verified, so
    // the inner share checksum only fails under fault injection or memory
    // corruption.
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(checksum, crc32(exp0, num_words * sizeof(uint32_t)));

  // Set mode and (if using a custom exponent) public exponent e.
  HARDENED_TRY(rsa_init_otbn(mode));
  if (pub_exp != 0) {
    const otbn_addr_t kOtbnVarRsaE = OTBN_ADDR_T_INIT(run_rsa, rsa_e);
    HARDENED_TRY(otbn_dmem_write(1, &pub_exp, kOtbnVarRsaE));
  }

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
                                  uint32_t exp, const uint32_t *modulus) {
  rsa_otbn_modes_t m;
  HARDENED_TRY(rsa_get_otbn_modes(size, &m));
  size_t num_words = m.num_words;
  uint32_t mode = (exp == 0) ? m.modexp_f4 : m.modexp_e;

  // Set mode and (if using a custom exponent) public exponent e.
  HARDENED_TRY(rsa_init_otbn(mode));
  if (exp != 0) {
    const otbn_addr_t kOtbnVarRsaE = OTBN_ADDR_T_INIT(run_rsa, rsa_e);
    HARDENED_TRY(otbn_dmem_write(1, &exp, kOtbnVarRsaE));
  }

  // Set the base and the modulus n.
  const otbn_addr_t kOtbnVarRsaInOut = OTBN_ADDR_T_INIT(run_rsa, inout);
  HARDENED_TRY(otbn_dmem_write(num_words, base, kOtbnVarRsaInOut));
  const otbn_addr_t kOtbnVarRsaN = OTBN_ADDR_T_INIT(run_rsa, rsa_n);
  HARDENED_TRY(otbn_dmem_write(num_words, modulus, kOtbnVarRsaN));

  // Start OTBN.
  return otbn_execute();
}

static status_t keygen_size_to_params(rsa_size_t size, uint32_t *mode,
                                      size_t *num_words) {
  rsa_otbn_modes_t m;
  HARDENED_TRY(rsa_get_otbn_modes(size, &m));
  *mode = m.keygen;
  *num_words = m.num_words;
  return OTCRYPTO_OK;
}

status_t rsa_size_to_num_words(rsa_size_t size, size_t *num_words) {
  uint32_t unused_mode = 0;
  return keygen_size_to_params(size, &unused_mode, num_words);
}

status_t rsa_modexp_finalize_size(rsa_size_t size, uint32_t *result) {
  size_t expected_words = 0;
  HARDENED_TRY(rsa_size_to_num_words(size, &expected_words));
  return rsa_modexp_finalize(expected_words, result);
}

status_t rsa_keygen_start(rsa_size_t size) {
  uint32_t mode = 0;
  size_t unused_words = 0;
  HARDENED_TRY(keygen_size_to_params(size, &mode, &unused_words));
  return keygen_start(mode);
}

status_t rsa_prime_check(rsa_size_t size, const uint32_t *prime_candidate,
                         hardened_bool_t *prime_ok) {
  *prime_ok = kHardenedBoolFalse;
  uint32_t mode = 0;
  size_t num_words = 0;
  HARDENED_TRY(keygen_size_to_params(size, &mode, &num_words));
  size_t prime_words = num_words / 2;

  uint32_t det = kHardenedBoolTrue;
  HARDENED_TRY(rsa_init_otbn(mode));
  HARDENED_TRY(otbn_dmem_write(1, &det, OTBN_ADDR_T_INIT(run_rsa, rsa_e)));
  HARDENED_TRY(otbn_dmem_set(1, 0, OTBN_ADDR_T_INIT(run_rsa, rsa_p)));
  HARDENED_TRY(otbn_dmem_write(prime_words, prime_candidate,
                               OTBN_ADDR_T_INIT(run_rsa, rsa_n)));
  HARDENED_TRY(otbn_execute_sync());

  HARDENED_TRY(rsa_check_mode(mode));

  uint32_t ok = 0;
  HARDENED_TRY(otbn_dmem_read(1, OTBN_ADDR_T_INIT(run_rsa, ok), &ok));
  if (launder32(ok) == kHardenedBoolTrue) {
    HARDENED_CHECK_EQ(ok, kHardenedBoolTrue);
    HARDENED_TRY(rsa_check_mr_iters(OTBN_ADDR_T_INIT(run_rsa, mr_iter_p)));
    *prime_ok = kHardenedBoolTrue;
  } else {
    HARDENED_CHECK_NE(ok, kHardenedBoolTrue);
    *prime_ok = kHardenedBoolFalse;
  }
  return otbn_dmem_sec_wipe();
}

status_t rsa_create_n_from_primes(rsa_size_t size, const uint32_t *prime_p,
                                  const uint32_t *prime_q, uint32_t *modulus) {
  uint32_t mode = 0;
  size_t num_words = 0;
  HARDENED_TRY(keygen_size_to_params(size, &mode, &num_words));
  size_t prime_words = num_words / 2;

  uint32_t det = kHardenedBoolTrue;
  HARDENED_TRY(rsa_init_otbn(mode));
  HARDENED_TRY(otbn_dmem_write(1, &det, OTBN_ADDR_T_INIT(run_rsa, rsa_e)));
  HARDENED_TRY(
      otbn_dmem_write(prime_words, prime_p, OTBN_ADDR_T_INIT(run_rsa, rsa_p)));
  HARDENED_TRY(
      otbn_dmem_write(prime_words, prime_q, OTBN_ADDR_T_INIT(run_rsa, rsa_q)));
  HARDENED_TRY(otbn_execute_sync());

  HARDENED_TRY(rsa_check_otbn_status());
  HARDENED_TRY(rsa_check_mode(mode));

  HARDENED_TRY(
      otbn_dmem_read(num_words, OTBN_ADDR_T_INIT(run_rsa, rsa_n), modulus));
  return otbn_dmem_sec_wipe();
}

status_t rsa_keygen_finalize_size(rsa_size_t size, uint32_t *n, uint32_t *d0,
                                  uint32_t *d1, uint32_t *p, uint32_t *q) {
  uint32_t mode = 0;
  size_t expected_words = 0;
  HARDENED_TRY(keygen_size_to_params(size, &mode, &expected_words));
  return keygen_finalize(mode, expected_words, n, d0, d1, p, q);
}

status_t rsa_modulus_composite_check(rsa_size_t size, const uint32_t *modulus,
                                     hardened_bool_t *result) {
  *result = kHardenedBoolFalse;

  rsa_otbn_modes_t m;
  HARDENED_TRY(rsa_get_otbn_modes(size, &m));

  // Set the mode and the modulus, then run the check to completion.
  HARDENED_TRY(rsa_init_otbn(m.check_n));
  const otbn_addr_t kOtbnVarRsaN = OTBN_ADDR_T_INIT(run_rsa, rsa_n);
  HARDENED_TRY(otbn_dmem_write(m.num_words, modulus, kOtbnVarRsaN));
  HARDENED_TRY(otbn_execute_sync());

  // The test is variable time, so there is no instruction count check. Check
  // that the expected mode ran instead.
  if (!status_ok(rsa_check_mode(m.check_n))) {
    // COVERAGE (FI CM) The mode only changes under fault injection.
    HARDENED_TRY(otbn_dmem_sec_wipe());
    return OTCRYPTO_FATAL_ERR;
  }

  // `ok` holds a hardened boolean with the result of the check.
  uint32_t ok = 0;
  HARDENED_TRY(otbn_dmem_read(1, OTBN_ADDR_T_INIT(run_rsa, ok), &ok));
  HARDENED_TRY(otbn_dmem_sec_wipe());
  switch (launder32(ok)) {
    case kHardenedBoolTrue:
      HARDENED_CHECK_EQ(ok, kHardenedBoolTrue);
      *result = kHardenedBoolTrue;
      return OTCRYPTO_OK;
    case kHardenedBoolFalse:
      HARDENED_CHECK_EQ(ok, kHardenedBoolFalse);
      *result = kHardenedBoolFalse;
      return OTCRYPTO_OK;
    default:
      // COVERAGE (FI CM) Any other value indicates a fault.
      return OTCRYPTO_FATAL_ERR;
  }
}
