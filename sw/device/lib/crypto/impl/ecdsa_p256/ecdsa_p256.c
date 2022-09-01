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
OTBN_DECLARE_SYMBOL_ADDR(p256_ecdsa, d);     // The private key scalar d.
OTBN_DECLARE_SYMBOL_ADDR(p256_ecdsa, x_r);   // Verification result.

/* Declare symbols for DMEM pointers */
OTBN_DECLARE_SYMBOL_ADDR(p256_ecdsa, dptr_msg);
OTBN_DECLARE_SYMBOL_ADDR(p256_ecdsa, dptr_r);
OTBN_DECLARE_SYMBOL_ADDR(p256_ecdsa, dptr_s);
OTBN_DECLARE_SYMBOL_ADDR(p256_ecdsa, dptr_x);
OTBN_DECLARE_SYMBOL_ADDR(p256_ecdsa, dptr_y);
OTBN_DECLARE_SYMBOL_ADDR(p256_ecdsa, dptr_d);
OTBN_DECLARE_SYMBOL_ADDR(p256_ecdsa, dptr_x_r);

static const otbn_app_t kOtbnAppEcdsa = OTBN_APP_T_INIT(p256_ecdsa);
static const otbn_addr_t kOtbnVarEcdsaMode = OTBN_ADDR_T_INIT(p256_ecdsa, mode);
static const otbn_addr_t kOtbnVarEcdsaMsg = OTBN_ADDR_T_INIT(p256_ecdsa, msg);
static const otbn_addr_t kOtbnVarEcdsaR = OTBN_ADDR_T_INIT(p256_ecdsa, r);
static const otbn_addr_t kOtbnVarEcdsaS = OTBN_ADDR_T_INIT(p256_ecdsa, s);
static const otbn_addr_t kOtbnVarEcdsaX = OTBN_ADDR_T_INIT(p256_ecdsa, x);
static const otbn_addr_t kOtbnVarEcdsaY = OTBN_ADDR_T_INIT(p256_ecdsa, y);
static const otbn_addr_t kOtbnVarEcdsaD = OTBN_ADDR_T_INIT(p256_ecdsa, d);
static const otbn_addr_t kOtbnVarEcdsaXr = OTBN_ADDR_T_INIT(p256_ecdsa, x_r);
static const otbn_addr_t kOtbnVarEcdsaDptrMsg =
    OTBN_ADDR_T_INIT(p256_ecdsa, dptr_msg);
static const otbn_addr_t kOtbnVarEcdsaDptrR =
    OTBN_ADDR_T_INIT(p256_ecdsa, dptr_r);
static const otbn_addr_t kOtbnVarEcdsaDptrS =
    OTBN_ADDR_T_INIT(p256_ecdsa, dptr_s);
static const otbn_addr_t kOtbnVarEcdsaDptrX =
    OTBN_ADDR_T_INIT(p256_ecdsa, dptr_x);
static const otbn_addr_t kOtbnVarEcdsaDptrY =
    OTBN_ADDR_T_INIT(p256_ecdsa, dptr_y);
static const otbn_addr_t kOtbnVarEcdsaDptrD =
    OTBN_ADDR_T_INIT(p256_ecdsa, dptr_d);
static const otbn_addr_t kOtbnVarEcdsaDptrXr =
    OTBN_ADDR_T_INIT(p256_ecdsa, dptr_x_r);

/* Mode is represented by a single word, 1 for sign and 2 for verify */
static const uint32_t kOtbnEcdsaModeNumWords = 1;
static const uint32_t kOtbnEcdsaModeSign = 1;
static const uint32_t kOtbnEcdsaModeVerify = 2;

/**
 * Makes a single dptr in the P256 library point to where its value is stored.
 */
static otbn_error_t setup_data_pointer(otbn_t *otbn, otbn_addr_t dptr,
                                       otbn_addr_t value) {
  OTBN_RETURN_IF_ERROR(otbn_copy_data_to_otbn(otbn, 1, &value, dptr));
  return kOtbnErrorOk;
}

/**
 * Sets up all data pointers used by the P256 library to point to DMEM.
 *
 * The ECDSA P256 OTBN library makes use of "named" data pointers as part of
 * its calling convention, which are exposed as symbol starting with `dptr_`.
 * The DMEM locations these pointers refer to is not mandated by the P256
 * calling convention; the values can be placed anywhere in OTBN DMEM.
 *
 * For convenience, `p256_ecdsa.s` pre-allocates space for the data values.
 *
 * This function makes the data pointers refer to the pre-allocated DMEM
 * regions to store the actual values.
 */
static otbn_error_t setup_data_pointers(otbn_t *otbn) {
  OTBN_RETURN_IF_ERROR(
      setup_data_pointer(otbn, kOtbnVarEcdsaDptrMsg, kOtbnVarEcdsaMsg));
  OTBN_RETURN_IF_ERROR(
      setup_data_pointer(otbn, kOtbnVarEcdsaDptrR, kOtbnVarEcdsaR));
  OTBN_RETURN_IF_ERROR(
      setup_data_pointer(otbn, kOtbnVarEcdsaDptrS, kOtbnVarEcdsaS));
  OTBN_RETURN_IF_ERROR(
      setup_data_pointer(otbn, kOtbnVarEcdsaDptrX, kOtbnVarEcdsaX));
  OTBN_RETURN_IF_ERROR(
      setup_data_pointer(otbn, kOtbnVarEcdsaDptrY, kOtbnVarEcdsaY));
  OTBN_RETURN_IF_ERROR(
      setup_data_pointer(otbn, kOtbnVarEcdsaDptrD, kOtbnVarEcdsaD));
  OTBN_RETURN_IF_ERROR(
      setup_data_pointer(otbn, kOtbnVarEcdsaDptrXr, kOtbnVarEcdsaXr));
  return kOtbnErrorOk;
}

// TODO: This implementation waits while OTBN is processing; it should be
// modified to be non-blocking.
otbn_error_t ecdsa_p256_sign(const ecdsa_p256_message_digest_t *digest,
                             const ecdsa_p256_private_key_t *private_key,
                             ecdsa_p256_signature_t *result) {
  otbn_t otbn;
  otbn_init(&otbn);

  // Load the ECDSA/P-256 app and set up data pointers
  OTBN_RETURN_IF_ERROR(otbn_load_app(&otbn, kOtbnAppEcdsa));
  OTBN_RETURN_IF_ERROR(setup_data_pointers(&otbn));

  // Set mode so start() will jump into p256_ecdsa_sign.
  OTBN_RETURN_IF_ERROR(otbn_copy_data_to_otbn(
      &otbn, kOtbnEcdsaModeNumWords, &kOtbnEcdsaModeSign, kOtbnVarEcdsaMode));

  // Set the message digest.
  OTBN_RETURN_IF_ERROR(otbn_copy_data_to_otbn(&otbn, kP256ScalarNumWords,
                                              digest->h, kOtbnVarEcdsaMsg));

  // Set the private key.
  OTBN_RETURN_IF_ERROR(otbn_copy_data_to_otbn(&otbn, kP256ScalarNumWords,
                                              private_key->d, kOtbnVarEcdsaD));

  // Start the OTBN routine.
  OTBN_RETURN_IF_ERROR(otbn_execute_app(&otbn));

  // Spin here waiting for OTBN to complete.
  OTBN_RETURN_IF_ERROR(otbn_busy_wait_for_done(&otbn));

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
  otbn_t otbn;
  otbn_init(&otbn);

  // Load the ECDSA/P-256 app and set up data pointers
  OTBN_RETURN_IF_ERROR(otbn_load_app(&otbn, kOtbnAppEcdsa));
  OTBN_RETURN_IF_ERROR(setup_data_pointers(&otbn));

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
  OTBN_RETURN_IF_ERROR(otbn_busy_wait_for_done(&otbn));

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
