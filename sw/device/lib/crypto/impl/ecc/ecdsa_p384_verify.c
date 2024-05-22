// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/impl/ecc/ecdsa_p384_verify.h"

#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/hardened_memory.h"
#include "sw/device/lib/crypto/drivers/otbn.h"
#include "sw/device/lib/crypto/impl/ecc/p384_curve_point_valid.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

// Module ID for status codes.
#define MODULE_ID MAKE_MODULE_ID('p', '3', 'v')

OTBN_DECLARE_APP_SYMBOLS(p384_ecdsa_verify);     // The OTBN ECDSA/P-384 app.
OTBN_DECLARE_SYMBOL_ADDR(p384_ecdsa_verify, x);  // Public key x-coordinate.
OTBN_DECLARE_SYMBOL_ADDR(p384_ecdsa_verify, y);  // Public key y-coordinate.
OTBN_DECLARE_SYMBOL_ADDR(p384_ecdsa_verify,
                         x_r);  // result of verify (x1 coordinate)
OTBN_DECLARE_SYMBOL_ADDR(p384_ecdsa_verify,
                         msg);                   // hash message to sign/verify
OTBN_DECLARE_SYMBOL_ADDR(p384_ecdsa_verify, r);  // r part of signature
OTBN_DECLARE_SYMBOL_ADDR(p384_ecdsa_verify, s);  // s part of signature

static const otbn_app_t kOtbnAppEcdsaVerify =
    OTBN_APP_T_INIT(p384_ecdsa_verify);
static const otbn_addr_t kOtbnVarEcdsaX =
    OTBN_ADDR_T_INIT(p384_ecdsa_verify, x);
static const otbn_addr_t kOtbnVarEcdsaY =
    OTBN_ADDR_T_INIT(p384_ecdsa_verify, y);
static const otbn_addr_t kOtbnVarEcdsaMsg =
    OTBN_ADDR_T_INIT(p384_ecdsa_verify, msg);
static const otbn_addr_t kOtbnVarEcdsaR =
    OTBN_ADDR_T_INIT(p384_ecdsa_verify, r);
static const otbn_addr_t kOtbnVarEcdsaS =
    OTBN_ADDR_T_INIT(p384_ecdsa_verify, s);
static const otbn_addr_t kOtbnVarEcdsaRnd =
    OTBN_ADDR_T_INIT(p384_ecdsa_verify, x_r);

status_t ecdsa_p384_verify_start(const ecdsa_p384_signature_t *signature,
                                 const uint32_t digest[kP384ScalarWords],
                                 const p384_point_t *public_key) {
  // Check if public key is valid
  HARDENED_TRY(p384_curve_point_validate_start(public_key));
  HARDENED_TRY(p384_curve_point_validate_finalize());

  // Load the ECDSA/P-384 app
  HARDENED_TRY(otbn_load_app(kOtbnAppEcdsaVerify));

  // Set the message digest.
  HARDENED_TRY(set_message_digest(digest, kOtbnVarEcdsaMsg));

  // Set the signature R.
  HARDENED_TRY(otbn_dmem_write(kP384ScalarWords, signature->r, kOtbnVarEcdsaR));

  // Set the signature S.
  HARDENED_TRY(otbn_dmem_write(kP384ScalarWords, signature->s, kOtbnVarEcdsaS));

  // Set the public key x coordinate.
  HARDENED_TRY(otbn_dmem_write(kP384CoordWords, public_key->x, kOtbnVarEcdsaX));

  // Set the public key y coordinate.
  HARDENED_TRY(otbn_dmem_write(kP384CoordWords, public_key->y, kOtbnVarEcdsaY));

  // Start the OTBN routine.
  return otbn_execute();
}

status_t ecdsa_p384_verify_finalize(const ecdsa_p384_signature_t *signature,
                                    hardened_bool_t *result) {
  // Spin here waiting for OTBN to complete.
  HARDENED_TRY(otbn_busy_wait_for_done());

  // Read x_r (recovered R) out of OTBN dmem.
  uint32_t x_r[kP384ScalarWords];
  HARDENED_TRY(otbn_dmem_read(kP384ScalarWords, kOtbnVarEcdsaRnd, x_r));

  *result = hardened_memeq(x_r, signature->r, kP384ScalarWords);

  // Wipe DMEM.
  HARDENED_TRY(otbn_dmem_sec_wipe());

  return OTCRYPTO_OK;
}
