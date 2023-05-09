// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/impl/status.h"

#include "sw/device/lib/base/hardened_status.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/crypto/include/datatypes.h"

/**
 * Call `HARDENED_TRY` on the status, and return it if the try passes.
 *
 * `HARDENED_TRY` forces the error bit to 1 if the value doesn't pass the
 * hardened check, so this routine ensures that values which are not exactly
 * the hardened-OK value will be errors.
 *
 * @param status Status to check
 * @return Same status with error bit always set if `HARDENED_TRY` failed.
 */
static status_t do_hardened_try(status_t status) {
  HARDENED_TRY(status);
  return status;
}

crypto_status_t crypto_status_interpret(status_t status) {
  status = do_hardened_try(status);
  return (crypto_status_t) status.value;
}
