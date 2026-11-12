// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/kmac_testutils.h"

#include "sw/device/lib/dif/dif_kmac.h"
#include "sw/device/lib/testing/test_framework/check.h"

status_t kmac_testutils_config(dif_kmac_t *kmac, bool sideload) {
  dif_kmac_config_t config = {
      // Always mask Keccak operations, even if not processing a secret key.
      .entropy_fast_process = false,
      // Leave message as the little-endian default.
      .message_big_endian = false,
      // Leave output as the little-endian default.
      .output_big_endian = false,
      // Use a sideloaded key if the caller requested to.
      .sideload = sideload,
      // Mask the message upon loading.
      .msg_mask = true,
  };

  dif_kmac_entropy_config_t entropy_config = {
      // Use software-provided "entropy" to avoid waiting for EDN.
      .entropy_mode = kDifKmacEntropyModeSoftware,
      // Don't ignore reseed requests from software.
      .ignore_cmd_entropy_req = false,
      // This can be ignored as we use the Software Mode.
      .edn_mode_refresh_threshold = 0,
      // Any seed is suitable for testing.
      .sw_mode_entropy_seed = {0xb153e3fe, 0x09596819, 0x3e85a6e8, 0xb6dcdaba,
                               0x50dc409c, 0x11e1ebd1},
  };

  TRY(dif_kmac_configure(kmac, config));
  TRY(dif_kmac_configure_entropy(kmac, entropy_config));
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
