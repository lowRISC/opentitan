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

enum {
  /* Fixed public exponent for generated keys. This exponent is 2^16 + 1, also
     known as "F4" because it's the fourth Fermat number. */
  kFixedPublicExponent = 65537,
  /* Number of words used to represent the application mode. */
  kOtbnRsaModeWords = 1,
};

status_t rsa_keygen_from_cofactor_2048_start(
    const rsa_2048_public_key_t *public_key,
    const rsa_2048_cofactor_t *cofactor) {
  // Load the RSA key generation app. Fails if OTBN is non-idle.
  HARDENED_TRY(otbn_load_app(kOtbnAppRsaKeygen));

  // Write the modulus and cofactor into DMEM.
  HARDENED_TRY(otbn_dmem_write(ARRAYSIZE(public_key->n.data),
                               public_key->n.data, kOtbnVarRsaN));
  HARDENED_TRY(otbn_dmem_write(ARRAYSIZE(cofactor->data), cofactor->data,
                               kOtbnVarRsaCofactor));

  // Set mode and start OTBN.
  uint32_t mode = kOtbnRsaModeCofactor2048;
  HARDENED_TRY(otbn_dmem_write(kOtbnRsaModeWords, &mode, kOtbnVarRsaMode));
  return otbn_execute();
}

status_t rsa_keygen_from_cofactor_2048_finalize(
    rsa_2048_public_key_t *public_key, rsa_2048_private_key_t *private_key) {
  // Spin here waiting for OTBN to complete.
  HARDENED_TRY_WIPE_DMEM(otbn_busy_wait_for_done());

  // Read the mode from OTBN dmem and panic if it's not as expected.
  uint32_t act_mode = 0;
  HARDENED_TRY_WIPE_DMEM(
      otbn_dmem_read(kOtbnRsaModeWords, kOtbnVarRsaMode, &act_mode));
  if (act_mode != kOtbnRsaModeCofactor2048) {
    HARDENED_TRY(otbn_dmem_sec_wipe());
    return OTCRYPTO_FATAL_ERR;
  }
  HARDENED_CHECK_EQ(launder32(act_mode), kOtbnRsaModeCofactor2048);

  // Read the public modulus (n) from OTBN dmem.
  HARDENED_TRY_WIPE_DMEM(
      otbn_dmem_read(kRsa2048NumWords, kOtbnVarRsaN, private_key->n.data));

  // Read the first share of the private exponent (d) from OTBN dmem.
  HARDENED_TRY(
      otbn_dmem_read(kRsa2048NumWords, kOtbnVarRsaD0, private_key->d0.data));

  // Read the second share of the private exponent (d) from OTBN dmem.
  HARDENED_TRY(
      otbn_dmem_read(kRsa2048NumWords, kOtbnVarRsaD1, private_key->d1.data));

  // Copy the modulus to the public key.
  HARDENED_TRY(hardened_memcpy(public_key->n.data, private_key->n.data,
                               ARRAYSIZE(private_key->n.data)));

  // Wipe DMEM.
  return otbn_dmem_sec_wipe();
}
