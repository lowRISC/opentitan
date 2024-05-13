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

OTBN_DECLARE_APP_SYMBOLS(p384_ecdsa_sign);  // The OTBN ECDSA/P-384 app.
OTBN_DECLARE_SYMBOL_ADDR(p384_ecdsa_sign, d0);   // private key first share
OTBN_DECLARE_SYMBOL_ADDR(p384_ecdsa_sign, d1);   // private key second share
OTBN_DECLARE_SYMBOL_ADDR(p384_ecdsa_sign, msg);  // hash message to sign/verify
OTBN_DECLARE_SYMBOL_ADDR(p384_ecdsa_sign, r);    // r part of signature
OTBN_DECLARE_SYMBOL_ADDR(p384_ecdsa_sign, s);    // s part of signature

static const otbn_app_t kOtbnAppEcdsaSign = OTBN_APP_T_INIT(p384_ecdsa_sign);
static const otbn_addr_t kOtbnVarEcdsaD0 =
    OTBN_ADDR_T_INIT(p384_ecdsa_sign, d0);
static const otbn_addr_t kOtbnVarEcdsaD1 =
    OTBN_ADDR_T_INIT(p384_ecdsa_sign, d1);
static const otbn_addr_t kOtbnVarEcdsaMsg =
    OTBN_ADDR_T_INIT(p384_ecdsa_sign, msg);
static const otbn_addr_t kOtbnVarEcdsaR =
    OTBN_ADDR_T_INIT(p384_ecdsa_sign, r);
static const otbn_addr_t kOtbnVarEcdsaS =
    OTBN_ADDR_T_INIT(p384_ecdsa_sign, s);

enum {
  /*
   * Mode is represented by a single word.
   */
  kOtbnEcdsaModeWords = 1,
  /*
   * Mode to generate a new random keypair.
   *
   * Value taken from `p384_ecdsa.s`.
   */
  kOtbnEcdsaModeKeygen = 0x3d4,
  /*
   * Mode to generate a signature.
   *
   * Value taken from `p384_ecdsa.s`.
   */
  kOtbnEcdsaModeSign = 0x15b,
  /*
   * Mode to verify a signature.
   *
   * Value taken from `p384_ecdsa.s`.
   */
  kOtbnEcdsaModeVerify = 0x727,
};

status_t ecdsa_p384_sign_start(const uint32_t digest[kP384ScalarWords],
                               const p384_masked_scalar_t *private_key) {
  // Load the ECDSA/P-384 app. Fails if OTBN is non-idle.
  HARDENED_TRY(otbn_load_app(kOtbnAppEcdsaSign));

  // Set the message digest.
  HARDENED_TRY(set_message_digest(digest, kOtbnVarEcdsaMsg));

  // Set the private key shares.
  HARDENED_TRY(
      p384_masked_scalar_write(private_key, kOtbnVarEcdsaD0, kOtbnVarEcdsaD1));

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
