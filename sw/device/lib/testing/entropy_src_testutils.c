// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
#include "sw/device/lib/testing/entropy_src_testutils.h"

#include "sw/device/lib/dif/dif_entropy_src.h"
#include "sw/device/lib/testing/test_framework/check.h"

#define MODULE_ID MAKE_MODULE_ID('e', 'n', 's')

status_t entropy_src_testutils_fw_override_enable(
    dif_entropy_src_t *entropy_src, uint8_t buffer_threshold,
    bool route_to_firmware, bool bypass_conditioner) {
  const dif_entropy_src_fw_override_config_t fw_override_config = {
      .entropy_insert_enable = true,
      .buffer_threshold = buffer_threshold,
  };
  TRY(dif_entropy_src_fw_override_configure(entropy_src, fw_override_config,
                                            kDifToggleEnabled));

  const dif_entropy_src_config_t config = {
      .fips_enable = true,
      .fips_flag = true,
      .rng_fips = true,
      .route_to_firmware = route_to_firmware,
      .bypass_conditioner = bypass_conditioner,
      .single_bit_mode = kDifEntropySrcSingleBitModeDisabled,
      .health_test_threshold_scope = false,
      .health_test_window_size = 0x0200,
      .alert_threshold = 2,
  };
  TRY(dif_entropy_src_configure(entropy_src, config, kDifToggleEnabled));
  return OK_STATUS();
}

status_t entropy_src_testutils_wait_for_state(
    const dif_entropy_src_t *entropy_src, dif_entropy_src_main_fsm_t state) {
  dif_entropy_src_main_fsm_t cur_state;

  do {
    TRY(dif_entropy_src_get_main_fsm_state(entropy_src, &cur_state));
  } while (cur_state != state);
  return OK_STATUS();
}

status_t entropy_src_testutils_drain_observe_fifo(
    dif_entropy_src_t *entropy_src) {
  // This value is arbitrary, it could be 1 but since there is some
  // overhead in dif_entropy_src_observe_fifo_nonblocking_read, it's better
  // to read several words every time to drain the FIFO quickly.
  const size_t kDrainCount = 32;
  size_t len;
  // Read from the FIFO until we get a short read which means that the FIFO was
  // emptied.
  do {
    len = kDrainCount;
    TRY(dif_entropy_src_observe_fifo_nonblocking_read(entropy_src, NULL, &len));
  } while (len == kDrainCount);

  return OK_STATUS();
}

status_t entropy_src_testutils_disable_health_tests(
    dif_entropy_src_t *entropy_src) {
  static dif_entropy_src_test_t kHealthTest[] = {
      kDifEntropySrcTestRepetitionCount,
      kDifEntropySrcTestRepetitionCountSymbol,
      kDifEntropySrcTestAdaptiveProportion, kDifEntropySrcTestBucket,
      kDifEntropySrcTestMarkov};
  for (size_t i = 0; i < ARRAYSIZE(kHealthTest); i++) {
    TRY(dif_entropy_src_health_test_configure(
        entropy_src,
        (dif_entropy_src_health_test_config_t){.test_type = kHealthTest[i],
                                               .high_threshold = 0xffffffff,
                                               .low_threshold = 0}));
  }

  return OK_STATUS();
}
