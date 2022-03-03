// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/dif/dif_base.h"
#include "sw/device/lib/dif/dif_clkmgr.h"
#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/check.h"
#include "sw/device/lib/testing/test_framework/ottf.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

const test_config_t kTestConfig;

typedef struct expected_count_info {
  int count;
  int variability;
} expected_count_info_t;

expected_count_info_t count_info[kDifClkmgrMeasureUsbFrequency + 1] = {
  {479, 3},
  {239, 3},
  {119, 3},
  {499, 3},
  {239, 3}
};

const int measurement_delay_us = 30;

bool test_main() {
  dif_clkmgr_t clkmgr;
  ibex_timeout_t timeout;
  dif_clkmgr_recov_err_codes_t err_codes;

  CHECK_DIF_OK(dif_clkmgr_init(
      mmio_region_from_addr(TOP_EARLGREY_CLKMGR_AON_BASE_ADDR), &clkmgr));

  // Enable cycle measurements.
  for (int i = 0; i <= kDifClkmgrMeasureUsbFrequency; ++i) {
    dif_clkmgr_measure_frequency_t clock = (dif_clkmgr_measure_frequency_t)i;
    CHECK_DIF_OK(dif_clkmgr_enable_measure_frequency(&clkmgr, clock,
                                        count_info[clock].count - count_info[clock].variability,
						     count_info[clock].count + count_info[clock].variability));
  }

  // Wait for some rounds of measurement.
  timeout = ibex_timeout_init(measurement_delay_us);
  while (true) {
    if (ibex_timeout_check(&timeout)) break;
  }
  CHECK_DIF_OK(dif_clkmgr_recov_err_code_get_codes(&clkmgr, &err_codes));
  if (err_codes) {
    LOG_ERROR("Unexpected recoverable error codes 0x%x", err_codes);
  }
  return true;
}
