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
  CHECK_DIF_OK(dif_rv_core_ibex_get_rnd_status(rv_core_ibex, &rnd_status));
  return rnd_status & kDifRvCoreIbexRndStatusValid;
}

uint32_t rv_core_ibex_testutils_get_rnd_data(
    const dif_rv_core_ibex_t *rv_core_ibex, uint32_t timeout_usec) {
  IBEX_SPIN_FOR(rv_core_ibex_testutils_is_rnd_data_valid(rv_core_ibex),
                timeout_usec);

  uint32_t rnd_data;
  CHECK_DIF_OK(dif_rv_core_ibex_read_rnd_data(rv_core_ibex, &rnd_data));
  CHECK(rnd_data != 0);
  CHECK(rnd_data != UINT32_MAX);
  return rnd_data;
}
