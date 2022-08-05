// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/kmac_testutils.h"

#include "sw/device/lib/dif/dif_kmac.h"
#include "sw/device/lib/testing/test_framework/check.h"

void kmac_testutils_config(dif_kmac_t *kmac, bool sideload) {
  dif_kmac_config_t config = {
      // Use software-provided "entropy" to avoid waiting for EDN.
      .entropy_mode = kDifKmacEntropyModeSoftware,
      // This option minimizes masking to improve speed.
      .entropy_fast_process = true,
      // No need to have real entropy for tests.
      .entropy_seed = {0},
      // Ignored because the entropy source is software.
      .entropy_reseed_interval = 0,
      // Ignored because the entropy source is software.
      .entropy_wait_timer = 0,
      // Leave message as the little-endian default.
      .message_big_endian = false,
      // Leave output as the little-endian default.
      .output_big_endian = false,
      // Use a sideloaded key if the caller requested to.
      .sideload = sideload,
      // Avoid masking the message to improve speed.
      .msg_mask = false,
  };

  CHECK_DIF_OK(dif_kmac_configure(kmac, config));
}

void kmac_testutils_kmac(const dif_kmac_t *kmac,
                         const dif_kmac_mode_kmac_t mode,
                         const dif_kmac_key_t *key, const char *custom_string,
                         const size_t custom_string_len, const char *message,
                         const size_t message_len, const size_t output_len,
                         uint32_t *output) {
  // Initialize customization string.
  dif_kmac_customization_string_t kmac_custom_string;
  CHECK_DIF_OK(dif_kmac_customization_string_init(
      custom_string, custom_string_len, &kmac_custom_string));

  // Start the KMAC operation.
  dif_kmac_operation_state_t operation_state;
  CHECK_DIF_OK(dif_kmac_mode_kmac_start(kmac, &operation_state, mode,
                                        output_len, key, &kmac_custom_string));

  // Pass the entire message to KMAC ("absorb" stage).
  CHECK_DIF_OK(
      dif_kmac_absorb(kmac, &operation_state, message, message_len, NULL));

  // Get the output ("squeeze" stage).
  CHECK_DIF_OK(
      dif_kmac_squeeze(kmac, &operation_state, output, output_len, NULL));

  // End the operation.
  CHECK_DIF_OK(dif_kmac_end(kmac, &operation_state));

  // Double-check that there were no errors.
  dif_kmac_error_t err;
  CHECK_DIF_OK(dif_kmac_get_error(kmac, &err));
  CHECK(err == kDifErrorNone);
}
