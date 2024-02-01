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

OTBN_DECLARE_APP_SYMBOLS(p384_ecdsa_verify);  // The OTBN ECDSA/P-384 app.
OTBN_DECLARE_SYMBOL_ADDR(p384_ecdsa_verify,
                         dptr_x);  // pointer to x-coordinate (dptr_x)
OTBN_DECLARE_SYMBOL_ADDR(p384_ecdsa_verify,
                         dptr_y);  // pointer to y-coordinate (dptr_y)
OTBN_DECLARE_SYMBOL_ADDR(p384_ecdsa_verify,
                         dptr_rnd);  // pointer to rnd (dptr_rnd)
OTBN_DECLARE_SYMBOL_ADDR(p384_ecdsa_verify,
                         dptr_msg);  // pointer to msg (dptr_msg)
OTBN_DECLARE_SYMBOL_ADDR(p384_ecdsa_verify, dptr_r);  // pointer to R (dptr_r)
OTBN_DECLARE_SYMBOL_ADDR(p384_ecdsa_verify, dptr_s);  // pointer to S (dptr_s)
OTBN_DECLARE_SYMBOL_ADDR(p384_ecdsa_verify, x);  // Public key x-coordinate.
OTBN_DECLARE_SYMBOL_ADDR(p384_ecdsa_verify, y);  // Public key y-coordinate.
OTBN_DECLARE_SYMBOL_ADDR(p384_ecdsa_verify,
                         rnd);  // result of verify (x1 coordinate)
OTBN_DECLARE_SYMBOL_ADDR(p384_ecdsa_verify,
                         msg);                   // hash message to sign/verify
OTBN_DECLARE_SYMBOL_ADDR(p384_ecdsa_verify, r);  // r part of signature
OTBN_DECLARE_SYMBOL_ADDR(p384_ecdsa_verify, s);  // s part of signature

static const otbn_app_t kOtbnAppEcdsaVerify =
    OTBN_APP_T_INIT(p384_ecdsa_verify);
static const otbn_addr_t kOtbnVarEcdsaDptrX =
    OTBN_ADDR_T_INIT(p384_ecdsa_verify, dptr_x);
static const otbn_addr_t kOtbnVarEcdsaDptrY =
    OTBN_ADDR_T_INIT(p384_ecdsa_verify, dptr_y);
static const otbn_addr_t kOtbnVarEcdsaDptrRnd =
    OTBN_ADDR_T_INIT(p384_ecdsa_verify, dptr_rnd);
static const otbn_addr_t kOtbnVarEcdsaDptrMsg =
    OTBN_ADDR_T_INIT(p384_ecdsa_verify, dptr_msg);
static const otbn_addr_t kOtbnVarEcdsaDptrR =
    OTBN_ADDR_T_INIT(p384_ecdsa_verify, dptr_r);
static const otbn_addr_t kOtbnVarEcdsaDptrS =
    OTBN_ADDR_T_INIT(p384_ecdsa_verify, dptr_s);
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
    OTBN_ADDR_T_INIT(p384_ecdsa_verify, rnd);

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

/**
 * Makes a single dptr in the P384 library point to where its value is stored.
 */
static void setup_data_pointer(const otbn_addr_t dptr,
                               const otbn_addr_t value) {
  otbn_dmem_write(sizeof(value) / sizeof(uint32_t), &value, dptr);
}

/**
 * Sets up all data pointers used by the P384 library to point to DMEM.
 *
 * The ECDSA P384 OTBN library makes use of "named" data pointers as part of
 * its calling convention, which are exposed as symbol starting with `dptr_`.
 * The DMEM locations these pointers refer to is not mandated by the P384
 * calling convention; the values can be placed anywhere in OTBN DMEM.
 *
 * This function makes the data pointers refer to the pre-allocated DMEM
 * regions to store the actual values.
 */
static void setup_data_pointers(void) {
  setup_data_pointer(kOtbnVarEcdsaDptrX, kOtbnVarEcdsaX);
  setup_data_pointer(kOtbnVarEcdsaDptrY, kOtbnVarEcdsaY);
  setup_data_pointer(kOtbnVarEcdsaDptrRnd, kOtbnVarEcdsaRnd);
  setup_data_pointer(kOtbnVarEcdsaDptrMsg, kOtbnVarEcdsaMsg);
  setup_data_pointer(kOtbnVarEcdsaDptrR, kOtbnVarEcdsaR);
  setup_data_pointer(kOtbnVarEcdsaDptrS, kOtbnVarEcdsaS);
}

status_t ecdsa_p384_verify_start(const ecdsa_p384_signature_t *signature,
                                 const uint32_t digest[kP384ScalarWords],
                                 const p384_point_t *public_key) {
  // Check if public key is valid
  HARDENED_TRY(p384_curve_point_validate_start(public_key));
  HARDENED_TRY(p384_curve_point_validate_finalize());

  // Load the ECDSA/P-384 app
  HARDENED_TRY(otbn_load_app(kOtbnAppEcdsaVerify));

  // Set up the data pointers
  setup_data_pointers();

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
  uint32_t rnd[kP384ScalarWords];
  HARDENED_TRY(otbn_dmem_read(kP384ScalarWords, kOtbnVarEcdsaRnd, rnd));

  *result = hardened_memeq(rnd, signature->r, kP384ScalarWords);

  // Wipe DMEM.
  HARDENED_TRY(otbn_dmem_sec_wipe());

  return OTCRYPTO_OK;
}
