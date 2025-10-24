// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/impl/rsa/run_rsa.h"

#include "sw/device/lib/base/hardened_memory.h"
#include "sw/device/lib/crypto/drivers/otbn.h"
#include "sw/device/lib/runtime/log.h"

// Module ID for status codes.
#define MODULE_ID MAKE_MODULE_ID('r', 'm', 'e')

// Declare the OTBN app.
OTBN_DECLARE_APP_SYMBOLS(run_rsa);
static const otbn_app_t kOtbnAppRsa = OTBN_APP_T_INIT(run_rsa);

// Declare offsets for input and output buffers.
OTBN_DECLARE_SYMBOL_ADDR(run_rsa, mode);    // Application mode.
OTBN_DECLARE_SYMBOL_ADDR(run_rsa, rsa_n);   // Public modulus n.
OTBN_DECLARE_SYMBOL_ADDR(run_rsa, rsa_d0);  // Private exponent d0.
OTBN_DECLARE_SYMBOL_ADDR(run_rsa, rsa_d1);  // Private exponent d1.
OTBN_DECLARE_SYMBOL_ADDR(run_rsa, inout);   // Input/output buffer.

static const otbn_addr_t kOtbnVarRsaMode = OTBN_ADDR_T_INIT(run_rsa, mode);
static const otbn_addr_t kOtbnVarRsaN = OTBN_ADDR_T_INIT(run_rsa, rsa_n);
static const otbn_addr_t kOtbnVarRsaD0 = OTBN_ADDR_T_INIT(run_rsa, rsa_d0);
static const otbn_addr_t kOtbnVarRsaD1 = OTBN_ADDR_T_INIT(run_rsa, rsa_d1);
static const otbn_addr_t kOtbnVarRsaInOut = OTBN_ADDR_T_INIT(run_rsa, inout);

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
static const uint32_t kMode2048Keygen =
    OTBN_ADDR_T_INIT(run_rsa, MODE_RSA_2048_KEYGEN);
static const uint32_t kMode3072Keygen =
    OTBN_ADDR_T_INIT(run_rsa, MODE_RSA_3072_KEYGEN);
static const uint32_t kMode4096Keygen =
    OTBN_ADDR_T_INIT(run_rsa, MODE_RSA_4096_KEYGEN);
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

enum {
  /**
   * Common RSA exponent with a specialized implementation.
   *
   * This exponent is 2^16 + 1, and called "F4" because it's the fourth Fermat
   * number.
   */
  kExponentF4 = 65537
};

status_t rsa_modexp_wait(size_t *num_words) {
  // Spin here waiting for OTBN to complete.
  HARDENED_TRY_WIPE_DMEM(otbn_busy_wait_for_done());

  // Read the application mode.
  uint32_t mode;
  HARDENED_TRY_WIPE_DMEM(otbn_dmem_read(1, kOtbnVarRsaMode, &mode));

  *num_words = 0;
  if (mode == kMode2048Modexp || mode == kMode2048ModexpF4) {
    *num_words = kRsa2048NumWords;
  } else if (mode == kMode3072Modexp || mode == kMode3072ModexpF4) {
    *num_words = kRsa3072NumWords;
  } else if (mode == kMode4096Modexp || mode == kMode4096ModexpF4) {
    *num_words = kRsa4096NumWords;
  } else {
    // Wipe DMEM.
    HARDENED_TRY(otbn_dmem_sec_wipe());
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
  HARDENED_TRY_WIPE_DMEM(rsa_modexp_wait(&num_words_inferred));

  // Check that the inferred result size matches expectations.
  if (num_words != num_words_inferred) {
    // Wipe DMEM.
    HARDENED_TRY(otbn_dmem_sec_wipe());
    return OTCRYPTO_FATAL_ERR;
  }
  HARDENED_CHECK_EQ(launder32(num_words), num_words_inferred);

  // Read the result.
  HARDENED_TRY_WIPE_DMEM(otbn_dmem_read(num_words, kOtbnVarRsaInOut, result));

  // Wipe DMEM.
  return otbn_dmem_sec_wipe();
}

status_t rsa_modexp_consttime_2048_start(const rsa_2048_int_t *base,
                                         const rsa_2048_int_t *exp0,
                                         const rsa_2048_int_t *exp1,
                                         const rsa_2048_int_t *modulus) {
  // Load the OTBN app. Fails if OTBN is not idle.
  HARDENED_TRY(otbn_load_app(kOtbnAppRsa));

  // Set mode.
  uint32_t mode = kMode2048Modexp;
  HARDENED_TRY(otbn_dmem_write(1, &mode, kOtbnVarRsaMode));

  // Set the base, the modulus n and private exponent d.
  HARDENED_TRY(otbn_dmem_write(kRsa2048NumWords, base->data, kOtbnVarRsaInOut));
  HARDENED_TRY(otbn_dmem_write(kRsa2048NumWords, modulus->data, kOtbnVarRsaN));
  HARDENED_TRY(otbn_dmem_write(kRsa2048NumWords, exp0->data, kOtbnVarRsaD0));
  HARDENED_TRY(otbn_dmem_write(kRsa2048NumWords, exp1->data, kOtbnVarRsaD1));

  // Start OTBN.
  return otbn_execute();
}

status_t rsa_modexp_vartime_2048_start(const rsa_2048_int_t *base,
                                       const rsa_2048_int_t *modulus) {
  // Load the OTBN app. Fails if OTBN is not idle.
  HARDENED_TRY(otbn_load_app(kOtbnAppRsa));

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
                                         const rsa_3072_int_t *exp0,
                                         const rsa_3072_int_t *exp1,
                                         const rsa_3072_int_t *modulus) {
  // Load the OTBN app. Fails if OTBN is not idle.
  HARDENED_TRY(otbn_load_app(kOtbnAppRsa));

  // Set mode.
  uint32_t mode = kMode3072Modexp;
  HARDENED_TRY(otbn_dmem_write(1, &mode, kOtbnVarRsaMode));

  // Set the base, the modulus n and private exponent d.
  HARDENED_TRY(otbn_dmem_write(kRsa3072NumWords, base->data, kOtbnVarRsaInOut));
  HARDENED_TRY(otbn_dmem_write(kRsa3072NumWords, modulus->data, kOtbnVarRsaN));
  HARDENED_TRY(otbn_dmem_write(kRsa3072NumWords, exp0->data, kOtbnVarRsaD0));
  HARDENED_TRY(otbn_dmem_write(kRsa3072NumWords, exp1->data, kOtbnVarRsaD1));

  // Start OTBN.
  return otbn_execute();
}

status_t rsa_modexp_vartime_3072_start(const rsa_3072_int_t *base,
                                       const rsa_3072_int_t *modulus) {
  // Load the OTBN app. Fails if OTBN is not idle.
  HARDENED_TRY(otbn_load_app(kOtbnAppRsa));

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
                                         const rsa_4096_int_t *exp0,
                                         const rsa_4096_int_t *exp1,
                                         const rsa_4096_int_t *modulus) {
  // Load the OTBN app. Fails if OTBN is not idle.
  HARDENED_TRY(otbn_load_app(kOtbnAppRsa));

  // Set mode.
  uint32_t mode = kMode4096Modexp;
  HARDENED_TRY(otbn_dmem_write(1, &mode, kOtbnVarRsaMode));

  // Set the base, the modulus n and private exponent d.
  HARDENED_TRY(otbn_dmem_write(kRsa4096NumWords, base->data, kOtbnVarRsaInOut));
  HARDENED_TRY(otbn_dmem_write(kRsa4096NumWords, modulus->data, kOtbnVarRsaN));
  HARDENED_TRY(otbn_dmem_write(kRsa4096NumWords, exp0->data, kOtbnVarRsaD0));
  HARDENED_TRY(otbn_dmem_write(kRsa4096NumWords, exp1->data, kOtbnVarRsaD1));

  // Start OTBN.
  return otbn_execute();
}

status_t rsa_modexp_vartime_4096_start(const rsa_4096_int_t *base,
                                       const rsa_4096_int_t *modulus) {
  // Load the OTBN app. Fails if OTBN is not idle.
  HARDENED_TRY(otbn_load_app(kOtbnAppRsa));

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
  HARDENED_TRY(otbn_load_app(kOtbnAppRsa));

  // Set mode and start OTBN.
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
 * @param[out] d Buffer for the private exponent.
 * @return OK or error.
 */
static status_t keygen_finalize(uint32_t exp_mode, size_t num_words,
                                uint32_t *n, uint32_t *d0, uint32_t *d1) {
  // Spin here waiting for OTBN to complete.
  HARDENED_TRY_WIPE_DMEM(otbn_busy_wait_for_done());

  // Read the mode from OTBN dmem and panic if it's not as expected.
  uint32_t act_mode = 0;
  HARDENED_TRY_WIPE_DMEM(otbn_dmem_read(1, kOtbnVarRsaMode, &act_mode));
  if (act_mode != exp_mode) {
    HARDENED_TRY(otbn_dmem_sec_wipe());
    return OTCRYPTO_FATAL_ERR;
  }
  HARDENED_CHECK_EQ(launder32(act_mode), exp_mode);

  // Read the public modulus (n) from OTBN dmem.
  HARDENED_TRY_WIPE_DMEM(otbn_dmem_read(num_words, kOtbnVarRsaN, n));

  // Read the first share of the private exponent (d) from OTBN dmem.
  HARDENED_TRY(otbn_dmem_read(num_words, kOtbnVarRsaD0, d0));

  // Read the second share of the private exponent (d) from OTBN dmem.
  HARDENED_TRY(otbn_dmem_read(num_words, kOtbnVarRsaD1, d1));

  // Wipe DMEM.
  return otbn_dmem_sec_wipe();
}

status_t rsa_keygen_2048_start(void) { return keygen_start(kMode2048Keygen); }

status_t rsa_keygen_2048_finalize(rsa_2048_public_key_t *public_key,
                                  rsa_2048_private_key_t *private_key) {
  HARDENED_TRY(keygen_finalize(kMode2048Keygen, kRsa2048NumWords,
                               private_key->n.data, private_key->d0.data,
                               private_key->d1.data));

  // Copy the modulus to the public key.
  HARDENED_TRY(hardened_memcpy(public_key->n.data, private_key->n.data,
                               ARRAYSIZE(private_key->n.data)));

  return OTCRYPTO_OK;
}

status_t rsa_keygen_3072_start(void) { return keygen_start(kMode3072Keygen); }

status_t rsa_keygen_3072_finalize(rsa_3072_public_key_t *public_key,
                                  rsa_3072_private_key_t *private_key) {
  HARDENED_TRY(keygen_finalize(kMode3072Keygen, kRsa3072NumWords,
                               private_key->n.data, private_key->d0.data,
                               private_key->d1.data));

  // Copy the modulus to the public key.
  HARDENED_TRY(hardened_memcpy(public_key->n.data, private_key->n.data,
                               ARRAYSIZE(private_key->n.data)));

  return OTCRYPTO_OK;
}

status_t rsa_keygen_4096_start(void) { return keygen_start(kMode4096Keygen); }

status_t rsa_keygen_4096_finalize(rsa_4096_public_key_t *public_key,
                                  rsa_4096_private_key_t *private_key) {
  HARDENED_TRY(keygen_finalize(kMode4096Keygen, kRsa4096NumWords,
                               private_key->n.data, private_key->d0.data,
                               private_key->d1.data));

  // Copy the modulus to the public key.
  HARDENED_TRY(hardened_memcpy(public_key->n.data, private_key->n.data,
                               ARRAYSIZE(private_key->n.data)));

  return OTCRYPTO_OK;
}
