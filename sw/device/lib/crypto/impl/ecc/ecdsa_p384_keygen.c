// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/impl/ecc/ecdsa_p384_keygen.h"

#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/hardened_memory.h"
#include "sw/device/lib/crypto/drivers/otbn.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

// Module ID for status codes.
#define MODULE_ID MAKE_MODULE_ID('p', '3', 'k')

// Declare the OTBN app.
OTBN_DECLARE_APP_SYMBOLS(p384_ecdsa_keygen);
static const otbn_app_t kOtbnAppEcdsaKeygen =
    OTBN_APP_T_INIT(p384_ecdsa_keygen);

// Declare offsets for input and output buffers.
OTBN_DECLARE_SYMBOL_ADDR(p384_ecdsa_keygen,
                         mode);  // ECDSA keygen application mode.
OTBN_DECLARE_SYMBOL_ADDR(p384_ecdsa_keygen, d0);  // Private key first share.
OTBN_DECLARE_SYMBOL_ADDR(p384_ecdsa_keygen, d1);  // Private key second share.
OTBN_DECLARE_SYMBOL_ADDR(p384_ecdsa_keygen, x);   // x-coordinate.
OTBN_DECLARE_SYMBOL_ADDR(p384_ecdsa_keygen, y);   // y-coordinate.

static const otbn_addr_t kOtbnVarEcdsaMode =
    OTBN_ADDR_T_INIT(p384_ecdsa_keygen, mode);
static const otbn_addr_t kOtbnVarEcdsaX =
    OTBN_ADDR_T_INIT(p384_ecdsa_keygen, x);
static const otbn_addr_t kOtbnVarEcdsaY =
    OTBN_ADDR_T_INIT(p384_ecdsa_keygen, y);
static const otbn_addr_t kOtbnVarEcdsaD0 =
    OTBN_ADDR_T_INIT(p384_ecdsa_keygen, d0);
static const otbn_addr_t kOtbnVarEcdsaD1 =
    OTBN_ADDR_T_INIT(p384_ecdsa_keygen, d1);

// Declare mode constants.
OTBN_DECLARE_SYMBOL_ADDR(p384_ecdsa_keygen, MODE_KEYGEN_RANDOM);
OTBN_DECLARE_SYMBOL_ADDR(p384_ecdsa_keygen, MODE_KEYGEN_FROM_SEED);
static const uint32_t kOtbnEcdsaModeKeygen =
    OTBN_ADDR_T_INIT(p384_ecdsa_keygen, MODE_KEYGEN_RANDOM);
static const uint32_t kOtbnEcdsaModeSideloadKeygen =
    OTBN_ADDR_T_INIT(p384_ecdsa_keygen, MODE_KEYGEN_FROM_SEED);

enum {
  /*
   * Mode is represented by a single word.
   */
  kOtbnEcdsaModeWords = 1,
};

status_t ecdsa_p384_keygen_start(void) {
  // Load the ECDSA/P-384 app. Fails if OTBN is non-idle.
  HARDENED_TRY(otbn_load_app(kOtbnAppEcdsaKeygen));

  // Set mode so start() will jump into sideload-keygen.
  uint32_t mode = kOtbnEcdsaModeKeygen;
  HARDENED_TRY(otbn_dmem_write(kOtbnEcdsaModeWords, &mode, kOtbnVarEcdsaMode));

  // Start the OTBN routine.
  return otbn_execute();
}

status_t ecdsa_p384_sideload_keygen_start(void) {
  // Load the ECDSA/P-384 app. Fails if OTBN is non-idle.
  HARDENED_TRY(otbn_load_app(kOtbnAppEcdsaKeygen));

  // Set mode so start() will jump into sideload-keygen.
  uint32_t mode = kOtbnEcdsaModeSideloadKeygen;
  HARDENED_TRY(otbn_dmem_write(kOtbnEcdsaModeWords, &mode, kOtbnVarEcdsaMode));

  // Start the OTBN routine.
  return otbn_execute();
}

status_t ecdsa_p384_keygen_finalize(p384_masked_scalar_t *private_key,
                                    p384_point_t *public_key) {
  // Spin here waiting for OTBN to complete.
  HARDENED_TRY(otbn_busy_wait_for_done());

  // Read the masked private key from OTBN dmem.
  HARDENED_TRY(otbn_dmem_read(kP384MaskedScalarShareWords, kOtbnVarEcdsaD0,
                              private_key->share0));
  HARDENED_TRY(otbn_dmem_read(kP384MaskedScalarShareWords, kOtbnVarEcdsaD1,
                              private_key->share1));

  // Read the public key from OTBN dmem.
  HARDENED_TRY(otbn_dmem_read(kP384CoordWords, kOtbnVarEcdsaX, public_key->x));
  HARDENED_TRY(otbn_dmem_read(kP384CoordWords, kOtbnVarEcdsaY, public_key->y));

  // Wipe DMEM.
  HARDENED_TRY(otbn_dmem_sec_wipe());

  return OTCRYPTO_OK;
}

status_t ecdsa_p384_sideload_keygen_finalize(p384_point_t *public_key) {
  // Spin here waiting for OTBN to complete.
  HARDENED_TRY(otbn_busy_wait_for_done());

  // Read the public key from OTBN dmem.
  HARDENED_TRY(otbn_dmem_read(kP384CoordWords, kOtbnVarEcdsaX, public_key->x));
  HARDENED_TRY(otbn_dmem_read(kP384CoordWords, kOtbnVarEcdsaY, public_key->y));

  // Wipe DMEM.
  HARDENED_TRY(otbn_dmem_sec_wipe());

  return OTCRYPTO_OK;
}
