// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/impl/ecdsa_p256/ecdsa_p256.h"

#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/crypto/drivers/otbn.h"
#include "sw/device/lib/crypto/impl/otbn_util.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

OTBN_DECLARE_APP_SYMBOLS(p256_ecdsa);        // The OTBN ECDSA/P-256 app.
OTBN_DECLARE_SYMBOL_ADDR(p256_ecdsa, mode);  // ECDSA mode (sign or verify).
OTBN_DECLARE_SYMBOL_ADDR(p256_ecdsa, msg);   // Message digest.
OTBN_DECLARE_SYMBOL_ADDR(p256_ecdsa, r);     // The signature scalar R.
OTBN_DECLARE_SYMBOL_ADDR(p256_ecdsa, s);     // The signature scalar S.
OTBN_DECLARE_SYMBOL_ADDR(p256_ecdsa, x);     // The public key x-coordinate.
OTBN_DECLARE_SYMBOL_ADDR(p256_ecdsa, y);     // The public key y-coordinate.
OTBN_DECLARE_SYMBOL_ADDR(p256_ecdsa,
                         d0);  // The private key scalar d (share 0).
OTBN_DECLARE_SYMBOL_ADDR(p256_ecdsa,
                         d1);  // The private key scalar d (share 1).
OTBN_DECLARE_SYMBOL_ADDR(p256_ecdsa, x_r);  // Verification result.

static const otbn_app_t kOtbnAppEcdsa = OTBN_APP_T_INIT(p256_ecdsa);
static const otbn_addr_t kOtbnVarEcdsaMode = OTBN_ADDR_T_INIT(p256_ecdsa, mode);
static const otbn_addr_t kOtbnVarEcdsaMsg = OTBN_ADDR_T_INIT(p256_ecdsa, msg);
static const otbn_addr_t kOtbnVarEcdsaR = OTBN_ADDR_T_INIT(p256_ecdsa, r);
static const otbn_addr_t kOtbnVarEcdsaS = OTBN_ADDR_T_INIT(p256_ecdsa, s);
static const otbn_addr_t kOtbnVarEcdsaX = OTBN_ADDR_T_INIT(p256_ecdsa, x);
static const otbn_addr_t kOtbnVarEcdsaY = OTBN_ADDR_T_INIT(p256_ecdsa, y);
static const otbn_addr_t kOtbnVarEcdsaD0 = OTBN_ADDR_T_INIT(p256_ecdsa, d0);
static const otbn_addr_t kOtbnVarEcdsaD1 = OTBN_ADDR_T_INIT(p256_ecdsa, d1);
static const otbn_addr_t kOtbnVarEcdsaXr = OTBN_ADDR_T_INIT(p256_ecdsa, x_r);

/* Mode is represented by a single word, 1 for sign and 2 for verify */
static const uint32_t kOtbnEcdsaModeNumWords = 1;
static const uint32_t kOtbnEcdsaModeSign = 1;
static const uint32_t kOtbnEcdsaModeVerify = 2;

// TODO: This implementation waits while OTBN is processing; it should be
// modified to be non-blocking.
otbn_error_t ecdsa_p256_sign(const ecdsa_p256_message_digest_t *digest,
                             const ecdsa_p256_private_key_t *private_key,
                             ecdsa_p256_signature_t *result) {
  // If OTBN is non-idle, return an error.
  OTBN_RETURN_IF_ERROR(otbn_assert_idle());

  otbn_t otbn;
  otbn_init(&otbn);

  // Load the ECDSA/P-256 app and set up data pointers
  OTBN_RETURN_IF_ERROR(otbn_load_app(&otbn, kOtbnAppEcdsa));

  // Set mode so start() will jump into p256_ecdsa_sign.
  OTBN_RETURN_IF_ERROR(otbn_copy_data_to_otbn(
      &otbn, kOtbnEcdsaModeNumWords, &kOtbnEcdsaModeSign, kOtbnVarEcdsaMode));

  // Set the message digest.
  OTBN_RETURN_IF_ERROR(otbn_copy_data_to_otbn(&otbn, kP256ScalarNumWords,
                                              digest->h, kOtbnVarEcdsaMsg));

  // Set the private key shares.
  OTBN_RETURN_IF_ERROR(otbn_copy_data_to_otbn(
      &otbn, kP256ScalarNumWords, private_key->d0, kOtbnVarEcdsaD0));
  OTBN_RETURN_IF_ERROR(otbn_copy_data_to_otbn(
      &otbn, kP256ScalarNumWords, private_key->d1, kOtbnVarEcdsaD1));

  // Start the OTBN routine.
  OTBN_RETURN_IF_ERROR(otbn_execute_app(&otbn));

  // Spin here waiting for OTBN to complete.
  OTBN_RETURN_IF_ERROR(otbn_busy_wait_for_done());

  // Read signature R out of OTBN dmem.
  OTBN_RETURN_IF_ERROR(otbn_copy_data_from_otbn(&otbn, kP256ScalarNumWords,
                                                kOtbnVarEcdsaR, result->r));

  // Read signature S out of OTBN dmem.
  OTBN_RETURN_IF_ERROR(otbn_copy_data_from_otbn(&otbn, kP256ScalarNumWords,
                                                kOtbnVarEcdsaS, result->s));

  // TODO: try to verify the signature, and return an error if verification
  // fails.

  return kOtbnErrorOk;
}

// TODO: This implementation waits while OTBN is processing; it should be
// modified to be non-blocking.
otbn_error_t ecdsa_p256_verify(const ecdsa_p256_signature_t *signature,
                               const ecdsa_p256_message_digest_t *digest,
                               const ecdsa_p256_public_key_t *public_key,
                               hardened_bool_t *result) {
  // If OTBN is non-idle, return an error.
  OTBN_RETURN_IF_ERROR(otbn_assert_idle());

  otbn_t otbn;
  otbn_init(&otbn);

  // Load the ECDSA/P-256 app and set up data pointers
  OTBN_RETURN_IF_ERROR(otbn_load_app(&otbn, kOtbnAppEcdsa));

  // Set mode so start() will jump into p256_ecdsa_verify.
  OTBN_RETURN_IF_ERROR(otbn_copy_data_to_otbn(
      &otbn, kOtbnEcdsaModeNumWords, &kOtbnEcdsaModeVerify, kOtbnVarEcdsaMode));

  // Set the message digest.
  OTBN_RETURN_IF_ERROR(otbn_copy_data_to_otbn(&otbn, kP256ScalarNumWords,
                                              digest->h, kOtbnVarEcdsaMsg));

  // Set the signature R.
  OTBN_RETURN_IF_ERROR(otbn_copy_data_to_otbn(&otbn, kP256ScalarNumWords,
                                              signature->r, kOtbnVarEcdsaR));

  // Set the signature S.
  OTBN_RETURN_IF_ERROR(otbn_copy_data_to_otbn(&otbn, kP256ScalarNumWords,
                                              signature->s, kOtbnVarEcdsaS));

  // Set the public key x coordinate.
  OTBN_RETURN_IF_ERROR(otbn_copy_data_to_otbn(&otbn, kP256CoordNumWords,
                                              public_key->x, kOtbnVarEcdsaX));

  // Set the public key y coordinate.
  OTBN_RETURN_IF_ERROR(otbn_copy_data_to_otbn(&otbn, kP256CoordNumWords,
                                              public_key->y, kOtbnVarEcdsaY));

  // Start the OTBN routine.
  OTBN_RETURN_IF_ERROR(otbn_execute_app(&otbn));

  // Spin here waiting for OTBN to complete.
  OTBN_RETURN_IF_ERROR(otbn_busy_wait_for_done());

  // Read x_r (recovered R) out of OTBN dmem.
  uint32_t x_r[kP256ScalarNumWords];
  OTBN_RETURN_IF_ERROR(otbn_copy_data_from_otbn(&otbn, kP256ScalarNumWords,
                                                kOtbnVarEcdsaXr, x_r));

  // TODO: Harden this memory comparison or do it in OTBN.
  // Check that x_r == R.
  *result = kHardenedBoolTrue;
  for (int i = 0; i < kP256ScalarNumWords; i++) {
    if (x_r[i] != signature->r[i]) {
      *result = kHardenedBoolFalse;
    }
  }

  return kOtbnErrorOk;
}
