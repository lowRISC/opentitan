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

OTBN_DECLARE_APP_SYMBOLS(p384_ecdsa_keygen);  // The OTBN ECDSA/P-384 app.
OTBN_DECLARE_SYMBOL_ADDR(p384_ecdsa_keygen, dptr_k0);  // Pointer to k0.
OTBN_DECLARE_SYMBOL_ADDR(p384_ecdsa_keygen, dptr_k1);  // Pointer to k1.
OTBN_DECLARE_SYMBOL_ADDR(p384_ecdsa_keygen, dptr_d0);  // Pointer to d0.
OTBN_DECLARE_SYMBOL_ADDR(p384_ecdsa_keygen, dptr_d1);  // Pointer to d1.
OTBN_DECLARE_SYMBOL_ADDR(p384_ecdsa_keygen, k0);  // Random scalar first share.
OTBN_DECLARE_SYMBOL_ADDR(p384_ecdsa_keygen, k1);  // Random scalar second share.
OTBN_DECLARE_SYMBOL_ADDR(p384_ecdsa_keygen, d0);  // Private key first share.
OTBN_DECLARE_SYMBOL_ADDR(p384_ecdsa_keygen, d1);  // Private key second share.
OTBN_DECLARE_SYMBOL_ADDR(p384_ecdsa_keygen,
                         dptr_x);  // pointer to x-coordinate (dptr_x)
OTBN_DECLARE_SYMBOL_ADDR(p384_ecdsa_keygen,
                         dptr_y);  // pointer to y-coordinate (dptr_y)
OTBN_DECLARE_SYMBOL_ADDR(p384_ecdsa_keygen, x);  // x-coordinate.
OTBN_DECLARE_SYMBOL_ADDR(p384_ecdsa_keygen, y);  // y-coordinate.

static const otbn_app_t kOtbnAppEcdsaKeygen =
    OTBN_APP_T_INIT(p384_ecdsa_keygen);
static const otbn_addr_t kOtbnVarEcdsaDptrX =
    OTBN_ADDR_T_INIT(p384_ecdsa_keygen, dptr_x);
static const otbn_addr_t kOtbnVarEcdsaDptrY =
    OTBN_ADDR_T_INIT(p384_ecdsa_keygen, dptr_y);
static const otbn_addr_t kOtbnVarEcdsaX =
    OTBN_ADDR_T_INIT(p384_ecdsa_keygen, x);
static const otbn_addr_t kOtbnVarEcdsaY =
    OTBN_ADDR_T_INIT(p384_ecdsa_keygen, y);
static const otbn_addr_t kOtbnVarEcdsaDptrK0 =
    OTBN_ADDR_T_INIT(p384_ecdsa_keygen, dptr_k0);
static const otbn_addr_t kOtbnVarEcdsaDptrK1 =
    OTBN_ADDR_T_INIT(p384_ecdsa_keygen, dptr_k1);
static const otbn_addr_t kOtbnVarEcdsaDptrD0 =
    OTBN_ADDR_T_INIT(p384_ecdsa_keygen, dptr_d0);
static const otbn_addr_t kOtbnVarEcdsaDptrD1 =
    OTBN_ADDR_T_INIT(p384_ecdsa_keygen, dptr_d1);
static const otbn_addr_t kOtbnVarEcdsaK0 =
    OTBN_ADDR_T_INIT(p384_ecdsa_keygen, k0);
static const otbn_addr_t kOtbnVarEcdsaK1 =
    OTBN_ADDR_T_INIT(p384_ecdsa_keygen, k1);
static const otbn_addr_t kOtbnVarEcdsaD0 =
    OTBN_ADDR_T_INIT(p384_ecdsa_keygen, d0);
static const otbn_addr_t kOtbnVarEcdsaD1 =
    OTBN_ADDR_T_INIT(p384_ecdsa_keygen, d1);

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
}

status_t ecdsa_p384_keygen_start(void) {
  // Load the ECDSA/P-384 app. Fails if OTBN is non-idle.
  HARDENED_TRY(otbn_load_app(kOtbnAppEcdsaKeygen));

  // Set up the data pointers
  setup_data_pointers();

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
