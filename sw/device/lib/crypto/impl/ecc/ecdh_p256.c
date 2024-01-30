// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/impl/ecc/ecdh_p256.h"

#include "sw/device/lib/crypto/drivers/otbn.h"
#include "sw/lib/sw/device/base/hardened.h"
#include "sw/lib/sw/device/base/hardened_memory.h"

#include "hw/top_darjeeling/sw/autogen/top_darjeeling.h"

// Module ID for status codes.
#define MODULE_ID MAKE_MODULE_ID('p', '2', 'x')

OTBN_DECLARE_APP_SYMBOLS(p256_ecdh);        // The OTBN ECDSH/P-256 app.
OTBN_DECLARE_SYMBOL_ADDR(p256_ecdh, mode);  // ECDH application mode.
OTBN_DECLARE_SYMBOL_ADDR(p256_ecdh, x);     // The public key x-coordinate.
OTBN_DECLARE_SYMBOL_ADDR(p256_ecdh, y);     // The public key y-coordinate.
OTBN_DECLARE_SYMBOL_ADDR(p256_ecdh,
                         d0);  // The private key scalar d (share 0).
OTBN_DECLARE_SYMBOL_ADDR(p256_ecdh,
                         d1);             // The private key scalar d (share 1).
OTBN_DECLARE_SYMBOL_ADDR(p256_ecdh, ok);  // Public key validity.

static const otbn_app_t kOtbnAppEcdh = OTBN_APP_T_INIT(p256_ecdh);
static const otbn_addr_t kOtbnVarEcdhMode = OTBN_ADDR_T_INIT(p256_ecdh, mode);
static const otbn_addr_t kOtbnVarEcdhX = OTBN_ADDR_T_INIT(p256_ecdh, x);
static const otbn_addr_t kOtbnVarEcdhY = OTBN_ADDR_T_INIT(p256_ecdh, y);
static const otbn_addr_t kOtbnVarEcdhD0 = OTBN_ADDR_T_INIT(p256_ecdh, d0);
static const otbn_addr_t kOtbnVarEcdhD1 = OTBN_ADDR_T_INIT(p256_ecdh, d1);
static const otbn_addr_t kOtbnVarEcdhOk = OTBN_ADDR_T_INIT(p256_ecdh, ok);

// Mode is represented by a single word. See `p256_ecdh.s` for values.
static const uint32_t kOtbnEcdhModeWords = 1;
static const uint32_t kOtbnEcdhModeKeypairRandom = 0x3f1;
static const uint32_t kOtbnEcdhModeSharedKey = 0x5ec;

status_t ecdh_p256_keypair_start(void) {
  // Load the ECDSA/P-256 app. Fails if OTBN is non-idle.
  HARDENED_TRY(otbn_load_app(kOtbnAppEcdh));

  // Set mode so start() will jump into keygen.
  HARDENED_TRY(otbn_dmem_write(kOtbnEcdhModeWords, &kOtbnEcdhModeKeypairRandom,
                               kOtbnVarEcdhMode));

  // Start the OTBN routine.
  return otbn_execute();
}

status_t ecdh_p256_keypair_finalize(p256_masked_scalar_t *private_key,
                                    p256_point_t *public_key) {
  // Spin here waiting for OTBN to complete.
  HARDENED_TRY(otbn_busy_wait_for_done());

  // Read the masked private key from OTBN dmem.
  HARDENED_TRY(otbn_dmem_read(kP256MaskedScalarShareWords, kOtbnVarEcdhD0,
                              private_key->share0));
  HARDENED_TRY(otbn_dmem_read(kP256MaskedScalarShareWords, kOtbnVarEcdhD1,
                              private_key->share1));

  // Read the public key from OTBN dmem.
  HARDENED_TRY(otbn_dmem_read(kP256CoordWords, kOtbnVarEcdhX, public_key->x));
  HARDENED_TRY(otbn_dmem_read(kP256CoordWords, kOtbnVarEcdhY, public_key->y));

  // Wipe DMEM.
  HARDENED_TRY(otbn_dmem_sec_wipe());

  return OTCRYPTO_OK;
}

status_t ecdh_p256_shared_key_start(const p256_masked_scalar_t *private_key,
                                    const p256_point_t *public_key) {
  // Load the ECDSA/P-256 app. Fails if OTBN is non-idle.
  HARDENED_TRY(otbn_load_app(kOtbnAppEcdh));

  // Set mode so start() will jump into shared-key generation.
  HARDENED_TRY(otbn_dmem_write(kOtbnEcdhModeWords, &kOtbnEcdhModeSharedKey,
                               kOtbnVarEcdhMode));

  // Set the private key shares.
  HARDENED_TRY(
      p256_masked_scalar_write(private_key, kOtbnVarEcdhD0, kOtbnVarEcdhD1));

  // Set the public key x coordinate.
  HARDENED_TRY(otbn_dmem_write(kP256CoordWords, public_key->x, kOtbnVarEcdhX));

  // Set the public key y coordinate.
  HARDENED_TRY(otbn_dmem_write(kP256CoordWords, public_key->y, kOtbnVarEcdhY));

  // Start the OTBN routine.
  return otbn_execute();
}

status_t ecdh_p256_shared_key_finalize(ecdh_p256_shared_key_t *shared_key) {
  // Spin here waiting for OTBN to complete.
  HARDENED_TRY(otbn_busy_wait_for_done());

  // Read the code indicating if the public key is valid.
  uint32_t ok;
  HARDENED_TRY(otbn_dmem_read(1, kOtbnVarEcdhOk, &ok));
  if (launder32(ok) != kHardenedBoolTrue) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(ok, kHardenedBoolTrue);

  // Read the shares of the key from OTBN dmem (at vars x and y).
  HARDENED_TRY(
      otbn_dmem_read(kP256CoordWords, kOtbnVarEcdhX, shared_key->share0));
  HARDENED_TRY(
      otbn_dmem_read(kP256CoordWords, kOtbnVarEcdhY, shared_key->share1));

  // Wipe DMEM.
  HARDENED_TRY(otbn_dmem_sec_wipe());

  return OTCRYPTO_OK;
}
