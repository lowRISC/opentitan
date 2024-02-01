// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/impl/ecc/ecdh_p384.h"

#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/hardened_memory.h"
#include "sw/device/lib/crypto/drivers/otbn.h"
#include "sw/device/lib/crypto/impl/ecc/p384_curve_point_valid.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

// Module ID for status codes.
#define MODULE_ID MAKE_MODULE_ID('p', '3', 'x')

OTBN_DECLARE_APP_SYMBOLS(p384_ecdh);          // The OTBN ECDSH/P-384 app.
OTBN_DECLARE_SYMBOL_ADDR(p384_ecdh, mode);    // ECDH application mode.
OTBN_DECLARE_SYMBOL_ADDR(p384_ecdh, dptr_x);  // The public key x-coordinate.
OTBN_DECLARE_SYMBOL_ADDR(p384_ecdh, dptr_y);  // The public key y-coordinate.
OTBN_DECLARE_SYMBOL_ADDR(p384_ecdh,
                         x);  // The pointer to public key x-coordinate.
OTBN_DECLARE_SYMBOL_ADDR(p384_ecdh,
                         y);  // The pointer to public key y-coordinate.
OTBN_DECLARE_SYMBOL_ADDR(
    p384_ecdh,
    dptr_d0);  // The pointer to private key scalar d (share 0).
OTBN_DECLARE_SYMBOL_ADDR(
    p384_ecdh,
    dptr_d1);  // The pointer to private key scalar d (share 1).
OTBN_DECLARE_SYMBOL_ADDR(p384_ecdh,
                         d0);  // The private key scalar d (share 0).
OTBN_DECLARE_SYMBOL_ADDR(p384_ecdh,
                         d1);  // The private key scalar d (share 1).

static const otbn_app_t kOtbnAppEcdh = OTBN_APP_T_INIT(p384_ecdh);
static const otbn_addr_t kOtbnVarEcdhMode = OTBN_ADDR_T_INIT(p384_ecdh, mode);
static const otbn_addr_t kOtbnVarEcdhDptrX =
    OTBN_ADDR_T_INIT(p384_ecdh, dptr_x);
static const otbn_addr_t kOtbnVarEcdhDptrY =
    OTBN_ADDR_T_INIT(p384_ecdh, dptr_y);
static const otbn_addr_t kOtbnVarEcdhX = OTBN_ADDR_T_INIT(p384_ecdh, x);
static const otbn_addr_t kOtbnVarEcdhY = OTBN_ADDR_T_INIT(p384_ecdh, y);
static const otbn_addr_t kOtbnVarEcdhDptrD0 =
    OTBN_ADDR_T_INIT(p384_ecdh, dptr_d0);
static const otbn_addr_t kOtbnVarEcdhDptrD1 =
    OTBN_ADDR_T_INIT(p384_ecdh, dptr_d1);
static const otbn_addr_t kOtbnVarEcdhD0 = OTBN_ADDR_T_INIT(p384_ecdh, d0);
static const otbn_addr_t kOtbnVarEcdhD1 = OTBN_ADDR_T_INIT(p384_ecdh, d1);

enum {
  /*
   * Mode is represented by a single word.
   */
  kOtbnEcdhModeWords = 1,
  /*
   * Mode to generate a new random keypair.
   */
  kOtbnEcdhModeKeypairRandom = 0x3f1,
  /*
   * Mode to generate a new shared key.
   */
  kOtbnEcdhModeSharedKey = 0x5ec,
  // TODO: kOtbnEcdhModeKeypairFromSeed = 0x29f;
  // TODO: kOtbnEcdhModeSharedKeyFromSeed = 0x74b;
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
 * The ECDH P384 OTBN library makes use of "named" data pointers as part of
 * its calling convention, which are exposed as symbol starting with `dptr_`.
 * The DMEM locations these pointers refer to is not mandated by the P384
 * calling convention; the values can be placed anywhere in OTBN DMEM.
 *
 * This function makes the data pointers refer to the pre-allocated DMEM
 * regions to store the actual values.
 */
static void setup_data_pointers(void) {
  setup_data_pointer(kOtbnVarEcdhDptrX, kOtbnVarEcdhX);
  setup_data_pointer(kOtbnVarEcdhDptrY, kOtbnVarEcdhY);
  setup_data_pointer(kOtbnVarEcdhDptrD0, kOtbnVarEcdhD0);
  setup_data_pointer(kOtbnVarEcdhDptrD1, kOtbnVarEcdhD1);
}

status_t ecdh_p384_keypair_start(void) {
  // Load the ECDH/P-384 app. Fails if OTBN is non-idle.
  HARDENED_TRY(otbn_load_app(kOtbnAppEcdh));

  // Set up the data pointers
  setup_data_pointers();

  // Set mode so start() will jump into keygen.
  uint32_t mode = kOtbnEcdhModeKeypairRandom;
  HARDENED_TRY(otbn_dmem_write(kOtbnEcdhModeWords, &mode, kOtbnVarEcdhMode));

  // Start the OTBN routine.
  return otbn_execute();
}

status_t ecdh_p384_keypair_finalize(p384_masked_scalar_t *private_key,
                                    p384_point_t *public_key) {
  // Spin here waiting for OTBN to complete.
  HARDENED_TRY(otbn_busy_wait_for_done());

  // Read the masked private key from OTBN dmem.
  HARDENED_TRY(otbn_dmem_read(kP384MaskedScalarShareWords, kOtbnVarEcdhD0,
                              private_key->share0));
  HARDENED_TRY(otbn_dmem_read(kP384MaskedScalarShareWords, kOtbnVarEcdhD1,
                              private_key->share1));

  // Read the public key from OTBN dmem.
  HARDENED_TRY(otbn_dmem_read(kP384CoordWords, kOtbnVarEcdhX, public_key->x));
  HARDENED_TRY(otbn_dmem_read(kP384CoordWords, kOtbnVarEcdhY, public_key->y));

  // Wipe DMEM.
  HARDENED_TRY(otbn_dmem_sec_wipe());

  return OTCRYPTO_OK;
}

status_t ecdh_p384_shared_key_start(const p384_masked_scalar_t *private_key,
                                    const p384_point_t *public_key) {
  // Check if public key is valid
  HARDENED_TRY(p384_curve_point_validate_start(public_key));
  HARDENED_TRY(p384_curve_point_validate_finalize());

  // Load the ECDH/P-384 app. Fails if OTBN is non-idle.
  HARDENED_TRY(otbn_load_app(kOtbnAppEcdh));

  // Set up the data pointers
  setup_data_pointers();

  // Set mode so start() will jump into shared-key generation.
  uint32_t mode = kOtbnEcdhModeSharedKey;
  HARDENED_TRY(otbn_dmem_write(kOtbnEcdhModeWords, &mode, kOtbnVarEcdhMode));

  // Set the private key shares.
  HARDENED_TRY(
      p384_masked_scalar_write(private_key, kOtbnVarEcdhD0, kOtbnVarEcdhD1));

  // Set the public key x coordinate.
  HARDENED_TRY(otbn_dmem_write(kP384CoordWords, public_key->x, kOtbnVarEcdhX));

  // Set the public key y coordinate.
  HARDENED_TRY(otbn_dmem_write(kP384CoordWords, public_key->y, kOtbnVarEcdhY));

  // Start the OTBN routine.
  return otbn_execute();
}

status_t ecdh_p384_shared_key_finalize(ecdh_p384_shared_key_t *shared_key) {
  // Spin here waiting for OTBN to complete.
  HARDENED_TRY(otbn_busy_wait_for_done());

  // Read the shares of the key from OTBN dmem (at vars x and y).
  HARDENED_TRY(
      otbn_dmem_read(kP384CoordWords, kOtbnVarEcdhX, shared_key->share0));
  HARDENED_TRY(
      otbn_dmem_read(kP384CoordWords, kOtbnVarEcdhY, shared_key->share1));

  // Wipe DMEM.
  HARDENED_TRY(otbn_dmem_sec_wipe());

  return OTCRYPTO_OK;
}
