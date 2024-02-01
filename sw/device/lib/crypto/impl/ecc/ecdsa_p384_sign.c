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
OTBN_DECLARE_SYMBOL_ADDR(p384_ecdsa_sign,
                         dptr_x);  // pointer to x-coordinate (dptr_x)
OTBN_DECLARE_SYMBOL_ADDR(p384_ecdsa_sign,
                         dptr_y);  // pointer to y-coordinate (dptr_y)
OTBN_DECLARE_SYMBOL_ADDR(p384_ecdsa_sign, dptr_k0);  // pointer to k0 (dptr_k0)
OTBN_DECLARE_SYMBOL_ADDR(p384_ecdsa_sign, dptr_k1);  // pointer to k1 (dptr_k1)
OTBN_DECLARE_SYMBOL_ADDR(p384_ecdsa_sign, dptr_d0);  // pointer to d0 (dptr_d0)
OTBN_DECLARE_SYMBOL_ADDR(p384_ecdsa_sign, dptr_d1);  // pointer to d1 (dptr_d1)
OTBN_DECLARE_SYMBOL_ADDR(p384_ecdsa_sign,
                         dptr_msg);                 // pointer to msg (dptr_msg)
OTBN_DECLARE_SYMBOL_ADDR(p384_ecdsa_sign, dptr_r);  // pointer to R (dptr_r)
OTBN_DECLARE_SYMBOL_ADDR(p384_ecdsa_sign, dptr_s);  // pointer to S (dptr_s)
OTBN_DECLARE_SYMBOL_ADDR(p384_ecdsa_sign, x);       // x-coordinate.
OTBN_DECLARE_SYMBOL_ADDR(p384_ecdsa_sign, y);       // y-coordinate.
OTBN_DECLARE_SYMBOL_ADDR(p384_ecdsa_sign, k0);      // random scalar first share
OTBN_DECLARE_SYMBOL_ADDR(p384_ecdsa_sign, k1);   // random scalar second share
OTBN_DECLARE_SYMBOL_ADDR(p384_ecdsa_sign, d0);   // private key first share
OTBN_DECLARE_SYMBOL_ADDR(p384_ecdsa_sign, d1);   // private key second share
OTBN_DECLARE_SYMBOL_ADDR(p384_ecdsa_sign, msg);  // hash message to sign/verify
OTBN_DECLARE_SYMBOL_ADDR(p384_ecdsa_sign, r);    // r part of signature
OTBN_DECLARE_SYMBOL_ADDR(p384_ecdsa_sign, s);    // s part of signature

static const otbn_app_t kOtbnAppEcdsaSign = OTBN_APP_T_INIT(p384_ecdsa_sign);
static const otbn_addr_t kOtbnVarEcdsaDptrX =
    OTBN_ADDR_T_INIT(p384_ecdsa_sign, dptr_x);
static const otbn_addr_t kOtbnVarEcdsaDptrY =
    OTBN_ADDR_T_INIT(p384_ecdsa_sign, dptr_y);
static const otbn_addr_t kOtbnVarEcdsaDptrK0 =
    OTBN_ADDR_T_INIT(p384_ecdsa_sign, dptr_k0);
static const otbn_addr_t kOtbnVarEcdsaDptrK1 =
    OTBN_ADDR_T_INIT(p384_ecdsa_sign, dptr_k1);
static const otbn_addr_t kOtbnVarEcdsaDptrD0 =
    OTBN_ADDR_T_INIT(p384_ecdsa_sign, dptr_d0);
static const otbn_addr_t kOtbnVarEcdsaDptrD1 =
    OTBN_ADDR_T_INIT(p384_ecdsa_sign, dptr_d1);
static const otbn_addr_t kOtbnVarEcdsaDptrMsg =
    OTBN_ADDR_T_INIT(p384_ecdsa_sign, dptr_msg);
static const otbn_addr_t kOtbnVarEcdsaDptrR =
    OTBN_ADDR_T_INIT(p384_ecdsa_sign, dptr_r);
static const otbn_addr_t kOtbnVarEcdsaDptrS =
    OTBN_ADDR_T_INIT(p384_ecdsa_sign, dptr_s);
static const otbn_addr_t kOtbnVarEcdsaX = OTBN_ADDR_T_INIT(p384_ecdsa_sign, x);
static const otbn_addr_t kOtbnVarEcdsaY = OTBN_ADDR_T_INIT(p384_ecdsa_sign, y);
static const otbn_addr_t kOtbnVarEcdsaK0 =
    OTBN_ADDR_T_INIT(p384_ecdsa_sign, k0);
static const otbn_addr_t kOtbnVarEcdsaK1 =
    OTBN_ADDR_T_INIT(p384_ecdsa_sign, k1);
static const otbn_addr_t kOtbnVarEcdsaD0 =
    OTBN_ADDR_T_INIT(p384_ecdsa_sign, d0);
static const otbn_addr_t kOtbnVarEcdsaD1 =
    OTBN_ADDR_T_INIT(p384_ecdsa_sign, d1);
static const otbn_addr_t kOtbnVarEcdsaMsg =
    OTBN_ADDR_T_INIT(p384_ecdsa_sign, msg);
otbn_addr_t kOtbnVarEcdsaR = OTBN_ADDR_T_INIT(p384_ecdsa_sign, r);
otbn_addr_t kOtbnVarEcdsaS = OTBN_ADDR_T_INIT(p384_ecdsa_sign, s);

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
  setup_data_pointer(kOtbnVarEcdsaDptrK0, kOtbnVarEcdsaK0);
  setup_data_pointer(kOtbnVarEcdsaDptrK1, kOtbnVarEcdsaK1);
  setup_data_pointer(kOtbnVarEcdsaDptrD0, kOtbnVarEcdsaD0);
  setup_data_pointer(kOtbnVarEcdsaDptrD1, kOtbnVarEcdsaD1);
  setup_data_pointer(kOtbnVarEcdsaDptrMsg, kOtbnVarEcdsaMsg);
  setup_data_pointer(kOtbnVarEcdsaDptrR, kOtbnVarEcdsaR);
  setup_data_pointer(kOtbnVarEcdsaDptrS, kOtbnVarEcdsaS);
}

status_t ecdsa_p384_sign_start(const uint32_t digest[kP384ScalarWords],
                               const p384_masked_scalar_t *private_key) {
  // Load the ECDSA/P-384 app. Fails if OTBN is non-idle.
  HARDENED_TRY(otbn_load_app(kOtbnAppEcdsaSign));

  // Set up the data pointers
  setup_data_pointers();

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
