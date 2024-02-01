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
                         dptr_x);  // The public key x-coordinate.
OTBN_DECLARE_SYMBOL_ADDR(p384_curve_point_valid,
                         dptr_y);  // The public key y-coordinate.
OTBN_DECLARE_SYMBOL_ADDR(p384_curve_point_valid,
                         x);  // The pointer to public key x-coordinate.
OTBN_DECLARE_SYMBOL_ADDR(p384_curve_point_valid,
                         y);  // The pointer to public key y-coordinate.

static const otbn_app_t kOtbnAppCpv = OTBN_APP_T_INIT(p384_curve_point_valid);
static const otbn_addr_t kOtbnVarCpvDptrX =
    OTBN_ADDR_T_INIT(p384_curve_point_valid, dptr_x);
static const otbn_addr_t kOtbnVarCpvDptrY =
    OTBN_ADDR_T_INIT(p384_curve_point_valid, dptr_y);
static const otbn_addr_t kOtbnVarCpvX =
    OTBN_ADDR_T_INIT(p384_curve_point_valid, x);
static const otbn_addr_t kOtbnVarCpvY =
    OTBN_ADDR_T_INIT(p384_curve_point_valid, y);

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
 * The Curve Point Valid P384 OTBN library makes use of "named" data pointers
 * as part of its calling convention, which are exposed as symbol starting
 * with `dptr_`. The DMEM locations these pointers refer to is not mandated
 * by the P384 calling convention; the values can be placed anywhere in OTBN
 * DMEM.
 *
 * This function makes the data pointers refer to the pre-allocated DMEM
 * regions to store the actual values.
 */
static void setup_data_pointers(void) {
  setup_data_pointer(kOtbnVarCpvDptrX, kOtbnVarCpvX);
  setup_data_pointer(kOtbnVarCpvDptrY, kOtbnVarCpvY);
}

status_t p384_curve_point_validate_start(const p384_point_t *public_key) {
  // Load the P-384 Curve Point Valid app. Fails if OTBN is non-idle.
  HARDENED_TRY(otbn_load_app(kOtbnAppCpv));

  // Set up the data pointers
  setup_data_pointers();

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
