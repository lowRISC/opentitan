// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/impl/ecc/ecdsa_p384_sign.h"

#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/hardened_memory.h"
#include "sw/device/lib/crypto/drivers/otbn.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

// Module ID for status codes.
#define MODULE_ID MAKE_MODULE_ID('p', '3', 's')

// Declare the OTBN app.
OTBN_DECLARE_APP_SYMBOLS(p384_ecdsa_sign);  // The OTBN ECDSA/P-384 app.
static const otbn_app_t kOtbnAppEcdsaSign = OTBN_APP_T_INIT(p384_ecdsa_sign);

// Declare offsets for input and output buffers.
OTBN_DECLARE_SYMBOL_ADDR(p384_ecdsa_sign,
                         mode);                  // ECDSA sign application mode.
OTBN_DECLARE_SYMBOL_ADDR(p384_ecdsa_sign, d0);   // private key first share
OTBN_DECLARE_SYMBOL_ADDR(p384_ecdsa_sign, d1);   // private key second share
OTBN_DECLARE_SYMBOL_ADDR(p384_ecdsa_sign, msg);  // hash message to sign/verify
OTBN_DECLARE_SYMBOL_ADDR(p384_ecdsa_sign, r);    // r part of signature
OTBN_DECLARE_SYMBOL_ADDR(p384_ecdsa_sign, s);    // s part of signature

static const otbn_addr_t kOtbnVarEcdsaMode =
    OTBN_ADDR_T_INIT(p384_ecdsa_sign, mode);
static const otbn_addr_t kOtbnVarEcdsaD0 =
    OTBN_ADDR_T_INIT(p384_ecdsa_sign, d0);
static const otbn_addr_t kOtbnVarEcdsaD1 =
    OTBN_ADDR_T_INIT(p384_ecdsa_sign, d1);
static const otbn_addr_t kOtbnVarEcdsaMsg =
    OTBN_ADDR_T_INIT(p384_ecdsa_sign, msg);
static const otbn_addr_t kOtbnVarEcdsaR = OTBN_ADDR_T_INIT(p384_ecdsa_sign, r);
static const otbn_addr_t kOtbnVarEcdsaS = OTBN_ADDR_T_INIT(p384_ecdsa_sign, s);

// Declare mode constants.
OTBN_DECLARE_SYMBOL_ADDR(p384_ecdsa_sign, MODE_SIGN);
OTBN_DECLARE_SYMBOL_ADDR(p384_ecdsa_sign, MODE_SIDELOAD_SIGN);
static const uint32_t kOtbnEcdsaModeSign =
    OTBN_ADDR_T_INIT(p384_ecdsa_sign, MODE_SIGN);
static const uint32_t kOtbnEcdsaModeSideloadSign =
    OTBN_ADDR_T_INIT(p384_ecdsa_sign, MODE_SIDELOAD_SIGN);

enum {
  /*
   * Mode is represented by a single word.
   */
  kOtbnEcdsaModeWords = 1,
};

status_t ecdsa_p384_sign_start(const uint32_t digest[kP384ScalarWords],
                               const p384_masked_scalar_t *private_key) {
  // Load the ECDSA/P-384 app. Fails if OTBN is non-idle.
  HARDENED_TRY(otbn_load_app(kOtbnAppEcdsaSign));

  // Set mode so start() will jump into sideloaded signing.
  uint32_t mode = kOtbnEcdsaModeSign;
  HARDENED_TRY(otbn_dmem_write(kOtbnEcdsaModeWords, &mode, kOtbnVarEcdsaMode));

  // Set the message digest.
  HARDENED_TRY(set_message_digest(digest, kOtbnVarEcdsaMsg));

  // Set the private key shares.
  HARDENED_TRY(
      p384_masked_scalar_write(private_key, kOtbnVarEcdsaD0, kOtbnVarEcdsaD1));

  // Start the OTBN routine.
  return otbn_execute();
}

status_t ecdsa_p384_sideload_sign_start(
    const uint32_t digest[kP384ScalarWords]) {
  // Load the ECDSA/P-384 app. Fails if OTBN is non-idle.
  HARDENED_TRY(otbn_load_app(kOtbnAppEcdsaSign));

  // Set mode so start() will jump into sideloaded signing.
  uint32_t mode = kOtbnEcdsaModeSideloadSign;
  HARDENED_TRY(otbn_dmem_write(kOtbnEcdsaModeWords, &mode, kOtbnVarEcdsaMode));

  // Set the message digest.
  HARDENED_TRY(set_message_digest(digest, kOtbnVarEcdsaMsg));

  // Start the OTBN routine.
  return otbn_execute();
}

status_t ecdsa_p384_sign_finalize(ecdsa_p384_signature_t *result) {
  // Spin here waiting for OTBN to complete.
  HARDENED_TRY(otbn_busy_wait_for_done());

  // Read signature R out of OTBN dmem.
  HARDENED_TRY(otbn_dmem_read(kP384ScalarWords, kOtbnVarEcdsaR, result->r));

  // Read signature S out of OTBN dmem.
  HARDENED_TRY(otbn_dmem_read(kP384ScalarWords, kOtbnVarEcdsaS, result->s));

  // Wipe DMEM.
  HARDENED_TRY(otbn_dmem_sec_wipe());

  return OTCRYPTO_OK;
}
