// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/impl/sm2/ecdh_sm2.h"

#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/hardened_memory.h"
#include "sw/device/lib/crypto/drivers/otbn.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

// Module ID for status codes.
#define MODULE_ID MAKE_MODULE_ID('p', '2', 'x')

OTBN_DECLARE_APP_SYMBOLS(sm2_ecdh);        // The OTBN ECDSH/P-256 app.
OTBN_DECLARE_SYMBOL_ADDR(sm2_ecdh, mode);  // ECDH application mode.
OTBN_DECLARE_SYMBOL_ADDR(sm2_ecdh, x);     // The public key x-coordinate.
OTBN_DECLARE_SYMBOL_ADDR(sm2_ecdh, y);     // The public key y-coordinate.
OTBN_DECLARE_SYMBOL_ADDR(sm2_ecdh,
                         d0);  // The private key scalar d (share 0).
OTBN_DECLARE_SYMBOL_ADDR(sm2_ecdh,
                         d1);  // The private key scalar d (share 1).

static const otbn_app_t kOtbnAppEcdh = OTBN_APP_T_INIT(sm2_ecdh);
static const otbn_addr_t kOtbnVarEcdhMode = OTBN_ADDR_T_INIT(sm2_ecdh, mode);
static const otbn_addr_t kOtbnVarEcdhX = OTBN_ADDR_T_INIT(sm2_ecdh, x);
static const otbn_addr_t kOtbnVarEcdhY = OTBN_ADDR_T_INIT(sm2_ecdh, y);
static const otbn_addr_t kOtbnVarEcdhD0 = OTBN_ADDR_T_INIT(sm2_ecdh, d0);
static const otbn_addr_t kOtbnVarEcdhD1 = OTBN_ADDR_T_INIT(sm2_ecdh, d1);

// Mode is represented by a single word. See `sm2_ecdh.s` for values.
static const uint32_t kOtbnEcdhModeWords = 1;
static const uint32_t kOtbnEcdhModeKeypairRandom = 0x3f1;
static const uint32_t kOtbnEcdhModeSharedKey = 0x5ec;
static const uint32_t kOtbnEcdhModeKeypairFromSeed = 0x29f;
static const uint32_t kOtbnEcdhModeSharedKeyFromSeed = 0x74b;

status_t ecdh_sm2_keypair_start(void) {
  // Load the ECDSA/P-256 app. Fails if OTBN is non-idle.
  HARDENED_TRY(otbn_load_app(kOtbnAppEcdh));

  // Set mode so start() will jump into keygen.
  HARDENED_TRY(otbn_dmem_write(kOtbnEcdhModeWords, &kOtbnEcdhModeKeypairRandom,
                               kOtbnVarEcdhMode));

  // Start the OTBN routine.
  return otbn_execute();
}

status_t ecdh_sm2_keypair_finalize(sm2_masked_scalar_t *private_key,
                                    sm2_point_t *public_key) {
  // Spin here waiting for OTBN to complete.
  HARDENED_TRY(otbn_busy_wait_for_done());

  // Read the masked private key from OTBN dmem.
  HARDENED_TRY(otbn_dmem_read(ksm2MaskedScalarShareWords, kOtbnVarEcdhD0,
                              private_key->share0));
  HARDENED_TRY(otbn_dmem_read(ksm2MaskedScalarShareWords, kOtbnVarEcdhD1,
                              private_key->share1));

  // Read the public key from OTBN dmem.
  HARDENED_TRY(otbn_dmem_read(ksm2CoordWords, kOtbnVarEcdhX, public_key->x));
  HARDENED_TRY(otbn_dmem_read(ksm2CoordWords, kOtbnVarEcdhY, public_key->y));

  // Wipe DMEM.
  HARDENED_TRY(otbn_dmem_sec_wipe());

  return OTCRYPTO_OK;
}

status_t ecdh_sm2_shared_key_start(const sm2_masked_scalar_t *private_key,
                                    const sm2_point_t *public_key) {
  // Load the ECDSA/P-256 app. Fails if OTBN is non-idle.
  HARDENED_TRY(otbn_load_app(kOtbnAppEcdh));

  // Set mode so start() will jump into shared-key generation.
  HARDENED_TRY(otbn_dmem_write(kOtbnEcdhModeWords, &kOtbnEcdhModeSharedKey,
                               kOtbnVarEcdhMode));

  // Set the private key shares.
  HARDENED_TRY(
      sm2_masked_scalar_write(private_key, kOtbnVarEcdhD0, kOtbnVarEcdhD1));

  // Set the public key x coordinate.
  HARDENED_TRY(otbn_dmem_write(ksm2CoordWords, public_key->x, kOtbnVarEcdhX));

  // Set the public key y coordinate.
  HARDENED_TRY(otbn_dmem_write(ksm2CoordWords, public_key->y, kOtbnVarEcdhY));

  // Start the OTBN routine.
  return otbn_execute();
}

status_t ecdh_sm2_shared_key_finalize(ecdh_sm2_shared_key_t *shared_key) {
  // Spin here waiting for OTBN to complete.
  HARDENED_TRY(otbn_busy_wait_for_done());

  // Read the shares of the key from OTBN dmem (at vars x and y).
  HARDENED_TRY(
      otbn_dmem_read(ksm2CoordWords, kOtbnVarEcdhX, shared_key->share0));
  HARDENED_TRY(
      otbn_dmem_read(ksm2CoordWords, kOtbnVarEcdhY, shared_key->share1));

  // Wipe DMEM.
  HARDENED_TRY(otbn_dmem_sec_wipe());

  return OTCRYPTO_OK;
}

status_t ecdh_sm2_sideload_keypair_start(void) {
  // Load the ECDSA/P-256 app. Fails if OTBN is non-idle.
  HARDENED_TRY(otbn_load_app(kOtbnAppEcdh));

  // Set mode so start() will jump into sideloaded keygen.
  HARDENED_TRY(otbn_dmem_write(
      kOtbnEcdhModeWords, &kOtbnEcdhModeKeypairFromSeed, kOtbnVarEcdhMode));

  // Start the OTBN routine.
  return otbn_execute();
}

status_t ecdh_sm2_sideload_keypair_finalize(sm2_point_t *public_key) {
  // Spin here waiting for OTBN to complete.
  HARDENED_TRY(otbn_busy_wait_for_done());

  // Read the public key from OTBN dmem.
  HARDENED_TRY(otbn_dmem_read(ksm2CoordWords, kOtbnVarEcdhX, public_key->x));
  HARDENED_TRY(otbn_dmem_read(ksm2CoordWords, kOtbnVarEcdhY, public_key->y));

  // Wipe DMEM.
  HARDENED_TRY(otbn_dmem_sec_wipe());

  return OTCRYPTO_OK;
}

status_t ecdh_sm2_sideload_shared_key_start(const sm2_point_t *public_key) {
  // Load the ECDSA/P-256 app. Fails if OTBN is non-idle.
  HARDENED_TRY(otbn_load_app(kOtbnAppEcdh));

  // Set mode so start() will jump into shared-key generation.
  HARDENED_TRY(otbn_dmem_write(
      kOtbnEcdhModeWords, &kOtbnEcdhModeSharedKeyFromSeed, kOtbnVarEcdhMode));

  // Set the public key x coordinate.
  HARDENED_TRY(otbn_dmem_write(ksm2CoordWords, public_key->x, kOtbnVarEcdhX));

  // Set the public key y coordinate.
  HARDENED_TRY(otbn_dmem_write(ksm2CoordWords, public_key->y, kOtbnVarEcdhY));

  // Start the OTBN routine.
  return otbn_execute();
}
