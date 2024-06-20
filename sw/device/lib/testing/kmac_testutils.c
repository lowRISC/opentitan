// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/kmac_testutils.h"

#include "sw/device/lib/dif/dif_kmac.h"
#include "sw/device/lib/testing/test_framework/check.h"

status_t kmac_testutils_config(dif_kmac_t *kmac, bool sideload) {
  dif_kmac_config_t config = {
      // Use software-provided "entropy" to avoid waiting for EDN.
      .entropy_mode = kDifKmacEntropyModeSoftware,
      // This option minimizes masking to improve speed.
      .entropy_fast_process = true,
      // No need to have real entropy for tests.
      .entropy_seed = {0},
      .entropy_hash_threshold = 0,
      // Ignored because the entropy source is software.
      .entropy_wait_timer = 0,
      // Leave message as the little-endian default.
      .entropy_prescaler = 0,
      .message_big_endian = false,
      // Leave output as the little-endian default.
      .output_big_endian = false,
      // Use a sideloaded key if the caller requested to.
      .sideload = sideload,
      // Avoid masking the message to improve speed.
      .msg_mask = false,
  };

  TRY(dif_kmac_configure(kmac, config));
  return OK_STATUS();
}

status_t kmac_testutils_kmac(const dif_kmac_t *kmac,
                             const dif_kmac_mode_kmac_t mode,
                             const dif_kmac_key_t *key,
                             const char *custom_string,
                             const size_t custom_string_len,
                             const char *message, const size_t message_len,
                             const size_t output_len, uint32_t *output,
                             uint32_t *capacity) {
  // Initialize customization string.
  dif_kmac_customization_string_t kmac_custom_string;
  TRY(dif_kmac_customization_string_init(custom_string, custom_string_len,
                                         &kmac_custom_string));

  // Start the KMAC operation and check that KMAC doesn't report an error.
  dif_kmac_operation_state_t operation_state;
  TRY(dif_kmac_mode_kmac_start(kmac, &operation_state, mode, output_len, key,
                               &kmac_custom_string));
  TRY(kmac_testutils_check_error(kmac));

  // Pass the entire message to KMAC ("absorb" stage) and check that KMAC
  // doesn't report an error.
  TRY(dif_kmac_absorb(kmac, &operation_state, message, message_len, NULL));
  TRY(kmac_testutils_check_error(kmac));

  // Get the output ("squeeze" stage) and check that KMAC doesn't report an
  // error.
  TRY(dif_kmac_squeeze(kmac, &operation_state, output, output_len, NULL,
                       capacity));
  TRY(kmac_testutils_check_error(kmac));

  // End the operation and check that KMAC doesn't report an error.
  TRY(dif_kmac_end(kmac, &operation_state));
  TRY(kmac_testutils_check_error(kmac));

  return OK_STATUS();
}

status_t kmac_testutils_check_error(const dif_kmac_t *kmac) {
  bool error;
  TRY(dif_kmac_has_error_occurred(kmac, &error));

  // If no error has occurred, return early with OK.
  if (!error) {
    return OK_STATUS();
  }

  // Obtain more information on the error.
  dif_kmac_error_t err;
  uint32_t info;
  TRY(dif_kmac_get_error(kmac, &err, &info));

  // Clear the error IRQ.
  TRY(dif_kmac_clear_err_irq(kmac));

  // Inform HW that we have handled the error.
  TRY(dif_kmac_err_processed(kmac));

  // Return with a status based on the error code.
  switch (err) {
    case kDifErrorKeyNotValid:
      return FAILED_PRECONDITION();
    default:
      return INTERNAL();
  }
}
