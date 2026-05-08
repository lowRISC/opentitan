// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/impl/rsa/run_rsa_key_from_cofactor.h"

#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/hardened_memory.h"
#include "sw/device/lib/crypto/drivers/otbn.h"

// Module ID for status codes.
#define MODULE_ID MAKE_MODULE_ID('r', 'k', 'g')

// Declare the OTBN app.
OTBN_DECLARE_APP_SYMBOLS(run_rsa_key_from_cofactor);
static const otbn_app_t kOtbnAppRsaKeygen =
    OTBN_APP_T_INIT(run_rsa_key_from_cofactor);

// Declare offsets for input and output buffers.
OTBN_DECLARE_SYMBOL_ADDR(run_rsa_key_from_cofactor, mode);  // Application mode.
OTBN_DECLARE_SYMBOL_ADDR(run_rsa_key_from_cofactor,
                         rsa_n);  // Public exponent n.
OTBN_DECLARE_SYMBOL_ADDR(run_rsa_key_from_cofactor,
                         rsa_d0);  // Private exponent d0.
OTBN_DECLARE_SYMBOL_ADDR(run_rsa_key_from_cofactor,
                         rsa_d1);  // Private exponent d1.
OTBN_DECLARE_SYMBOL_ADDR(run_rsa_key_from_cofactor,
                         rsa_cofactor);  // Cofactor p or q.

static const otbn_addr_t kOtbnVarRsaMode =
    OTBN_ADDR_T_INIT(run_rsa_key_from_cofactor, mode);
static const otbn_addr_t kOtbnVarRsaN =
    OTBN_ADDR_T_INIT(run_rsa_key_from_cofactor, rsa_n);
static const otbn_addr_t kOtbnVarRsaD0 =
    OTBN_ADDR_T_INIT(run_rsa_key_from_cofactor, rsa_d0);
static const otbn_addr_t kOtbnVarRsaD1 =
    OTBN_ADDR_T_INIT(run_rsa_key_from_cofactor, rsa_d1);
static const otbn_addr_t kOtbnVarRsaCofactor =
    OTBN_ADDR_T_INIT(run_rsa_key_from_cofactor, rsa_cofactor);

// Declare mode constants.
OTBN_DECLARE_SYMBOL_ADDR(run_rsa_key_from_cofactor, MODE_COFACTOR_RSA_2048);
static const uint32_t kOtbnRsaModeCofactor2048 =
    OTBN_ADDR_T_INIT(run_rsa_key_from_cofactor, MODE_COFACTOR_RSA_2048);

OTBN_DECLARE_SYMBOL_ADDR(run_rsa_key_from_cofactor, MODE_COFACTOR_RSA_3072);
static const uint32_t kOtbnRsaModeCofactor3072 =
    OTBN_ADDR_T_INIT(run_rsa_key_from_cofactor, MODE_COFACTOR_RSA_3072);

OTBN_DECLARE_SYMBOL_ADDR(run_rsa_key_from_cofactor, MODE_COFACTOR_RSA_4096);
static const uint32_t kOtbnRsaModeCofactor4096 =
    OTBN_ADDR_T_INIT(run_rsa_key_from_cofactor, MODE_COFACTOR_RSA_4096);

enum {
  /* Number of words used to represent the application mode. */
  kOtbnRsaModeWords = 1,
};

status_t rsa_keygen_from_cofactor_start(rsa_size_t size,
                                        const uint32_t *public_key_n,
                                        const uint32_t *cofactor) {
  // Load the RSA key generation app. Fails if OTBN is non-idle.
  HARDENED_TRY(otbn_load_app(kOtbnAppRsaKeygen));

  size_t num_words = 0;
  uint32_t mode = 0;

  switch (launder32(size)) {
    case kRsaSize2048:
      HARDENED_CHECK_EQ(size, kRsaSize2048);
      num_words = kRsa2048NumWords;
      mode = kOtbnRsaModeCofactor2048;
      break;
    case kRsaSize3072:
      HARDENED_CHECK_EQ(size, kRsaSize3072);
      num_words = kRsa3072NumWords;
      mode = kOtbnRsaModeCofactor3072;
      break;
    case kRsaSize4096:
      HARDENED_CHECK_EQ(size, kRsaSize4096);
      num_words = kRsa4096NumWords;
      mode = kOtbnRsaModeCofactor4096;
      break;
    default:
      HARDENED_TRAP();
      // COVERAGE (FI CM) Unreachable code, checked against fault injections.
      return OTCRYPTO_FATAL_ERR;
  }

  // Write the modulus and cofactor into DMEM. Note: The cofactor is half the
  // size of the modulus.
  HARDENED_TRY(otbn_dmem_write(num_words, public_key_n, kOtbnVarRsaN));
  HARDENED_TRY(otbn_dmem_write(num_words / 2, cofactor, kOtbnVarRsaCofactor));

  // Set mode and start OTBN.
  HARDENED_TRY(otbn_dmem_write(kOtbnRsaModeWords, &mode, kOtbnVarRsaMode));
  return otbn_execute();
}

status_t rsa_keygen_from_cofactor_finalize(rsa_size_t size,
                                           uint32_t *public_key_n,
                                           uint32_t *private_key_n,
                                           uint32_t *private_key_d0,
                                           uint32_t *private_key_d1) {
  // Spin here waiting for OTBN to complete.
  HARDENED_TRY_WIPE_DMEM(otbn_busy_wait_for_done());

  size_t num_words = 0;
  uint32_t exp_mode = 0;

  switch (launder32(size)) {
    case kRsaSize2048:
      HARDENED_CHECK_EQ(size, kRsaSize2048);
      num_words = kRsa2048NumWords;
      exp_mode = kOtbnRsaModeCofactor2048;
      break;
    case kRsaSize3072:
      HARDENED_CHECK_EQ(size, kRsaSize3072);
      num_words = kRsa3072NumWords;
      exp_mode = kOtbnRsaModeCofactor3072;
      break;
    case kRsaSize4096:
      HARDENED_CHECK_EQ(size, kRsaSize4096);
      num_words = kRsa4096NumWords;
      exp_mode = kOtbnRsaModeCofactor4096;
      break;
    default:
      HARDENED_TRAP();
      // COVERAGE (FI CM) Unreachable code, checked against fault injections.
      return OTCRYPTO_FATAL_ERR;
  }

  // Read the mode from OTBN dmem and panic if it's not as expected.
  uint32_t act_mode = 0;
  HARDENED_TRY_WIPE_DMEM(
      otbn_dmem_read(kOtbnRsaModeWords, kOtbnVarRsaMode, &act_mode));
  if (act_mode != exp_mode) {
    return OTCRYPTO_FATAL_ERR;
  }
  HARDENED_CHECK_EQ(launder32(act_mode), exp_mode);

  // Read the public modulus (n) from OTBN dmem.
  HARDENED_TRY_WIPE_DMEM(
      otbn_dmem_read(num_words, kOtbnVarRsaN, private_key_n));

  // Read the first share of the private exponent (d) from OTBN dmem.
  HARDENED_TRY_WIPE_DMEM(
      otbn_dmem_read(num_words, kOtbnVarRsaD0, private_key_d0));

  // Read the second share of the private exponent (d) from OTBN dmem.
  HARDENED_TRY_WIPE_DMEM(
      otbn_dmem_read(num_words, kOtbnVarRsaD1, private_key_d1));

  // Copy the modulus to the public key.
  HARDENED_TRY(hardened_memcpy(public_key_n, private_key_n, num_words));

  // Wipe DMEM.
  return otbn_dmem_sec_wipe();
}
