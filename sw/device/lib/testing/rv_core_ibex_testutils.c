// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/dif/dif_rv_core_ibex.h"
#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/testing/test_framework/check.h"

bool rv_core_ibex_testutils_is_rnd_data_valid(
    const dif_rv_core_ibex_t *rv_core_ibex) {
  dif_rv_core_ibex_rnd_status_t rnd_status;
  dif_result_t res = dif_rv_core_ibex_get_rnd_status(rv_core_ibex, &rnd_status);
  return (res == kDifOk) && (rnd_status & kDifRvCoreIbexRndStatusValid);
}

status_t rv_core_ibex_testutils_get_rnd_data(
    const dif_rv_core_ibex_t *rv_core_ibex, uint32_t timeout_usec,
    uint32_t *rnd_data) {
  IBEX_TRY_SPIN_FOR(rv_core_ibex_testutils_is_rnd_data_valid(rv_core_ibex),
                    timeout_usec);

  TRY(dif_rv_core_ibex_read_rnd_data(rv_core_ibex, rnd_data));
  TRY_CHECK(*rnd_data != 0);
  TRY_CHECK(*rnd_data != UINT32_MAX);
  return OK_STATUS();
}
