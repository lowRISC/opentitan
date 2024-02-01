// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_base.h"
#include "sw/device/lib/dif/dif_entropy_src.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/entropy_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

OTTF_DEFINE_TEST_CONFIG();

const size_t kEntropyDataChecks = 10;

bool test_main(void) {
  dif_entropy_src_t entropy_src;
  CHECK_DIF_OK(dif_entropy_src_init(
      mmio_region_from_addr(TOP_EARLGREY_ENTROPY_SRC_BASE_ADDR), &entropy_src));

  // Disable entropy for test purpose, as it has been turned on by ROM
  CHECK_DIF_OK(dif_entropy_src_set_enabled(&entropy_src, kDifToggleDisabled));

  // Setup fips grade entropy that can be read by firmware
  const dif_entropy_src_config_t config = {
      .fips_enable = true,
      .fips_flag = true,
      .rng_fips = true,
      .route_to_firmware = true,
      .single_bit_mode = kDifEntropySrcSingleBitModeDisabled,
      .health_test_threshold_scope = false, /*default*/
      .health_test_window_size = 0x0200,    /*default*/
      .alert_threshold = 2,                 /*default*/
  };

  // Re-enable entropy src
  CHECK_DIF_OK(
      dif_entropy_src_configure(&entropy_src, config, kDifToggleEnabled));

  // ensure health tests are actually running
  CHECK_STATUS_OK(entropy_testutils_wait_for_state(
      &entropy_src, kDifEntropySrcMainFsmStateContHTRunning));

  uint32_t entropy_data;
  uint32_t last_entropy_data = 0;
  for (uint32_t i = 0; i < kEntropyDataChecks; ++i) {
    // wait for entropy to become available and read
    while (dif_entropy_src_non_blocking_read(&entropy_src, &entropy_data) !=
           kDifOk)
      ;
    if (entropy_data == last_entropy_data) {
      LOG_FATAL("Received duplicate entropy, this should never happen");
    } else {
      last_entropy_data = entropy_data;
    }
  }

  uint32_t errors;
  CHECK_DIF_OK(dif_entropy_src_get_errors(&entropy_src, &errors));
  if (errors != 0) {
    LOG_FATAL("Error is non-zero, 0x%h", errors);
  } else {
    return true;
  }

  return false;
}
