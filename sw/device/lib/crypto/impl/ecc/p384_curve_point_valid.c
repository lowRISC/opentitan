// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/impl/ecc/p384_curve_point_valid.h"

#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/hardened_memory.h"
#include "sw/device/lib/crypto/drivers/otbn.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

// Module ID for status codes.
#define MODULE_ID MAKE_MODULE_ID('p', '3', 'c')

OTBN_DECLARE_APP_SYMBOLS(
    p384_curve_point_valid);  // The OTBN Curve Point Valid Check app.
OTBN_DECLARE_SYMBOL_ADDR(p384_curve_point_valid,
                         x);  // The public key x-coordinate.
OTBN_DECLARE_SYMBOL_ADDR(p384_curve_point_valid,
                         y);  // The public key y-coordinate.

static const otbn_app_t kOtbnAppCpv = OTBN_APP_T_INIT(p384_curve_point_valid);
static const otbn_addr_t kOtbnVarCpvX =
    OTBN_ADDR_T_INIT(p384_curve_point_valid, x);
static const otbn_addr_t kOtbnVarCpvY =
    OTBN_ADDR_T_INIT(p384_curve_point_valid, y);

status_t p384_curve_point_validate_start(const p384_point_t *public_key) {
  // Load the P-384 Curve Point Valid app. Fails if OTBN is non-idle.
  HARDENED_TRY(otbn_load_app(kOtbnAppCpv));

  // Set the public key x coordinate.
  HARDENED_TRY(otbn_dmem_write(kP384CoordWords, public_key->x, kOtbnVarCpvX));

  // Set the public key y coordinate.
  HARDENED_TRY(otbn_dmem_write(kP384CoordWords, public_key->y, kOtbnVarCpvY));

  // Start the OTBN routine.
  return otbn_execute();
}

status_t p384_curve_point_validate_finalize(void) {
  // Spin here waiting for OTBN to complete.
  HARDENED_TRY(otbn_busy_wait_for_done());

  // Wipe DMEM.
  HARDENED_TRY(otbn_dmem_sec_wipe());

  return OTCRYPTO_OK;
}
