// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_KMAC_TESTUTILS_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_KMAC_TESTUTILS_H_

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/dif/dif_kmac.h"

/**
 * Configure the KMAC block.
 *
 * This is a thin wrapper around `dif_kmac_configure`. It sets up a testing
 * configuration that prioritizes speed over security, since we don't care
 * about protecting test keys. For instance, it sets the entropy source to
 * software so KMAC doesn't wait for fresh entropy, and minimizes masking.
 *
 * @param kmac KMAC context.
 * @param sideload Whether to configure KMAC to read a sideloaded key.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
status_t kmac_testutils_config(dif_kmac_t *kmac, bool sideload);

/**
 * Runs the full KMAC operation.
 *
 * Assumes that the KMAC block has already been initialized and configured, and
 * that the sideloaded key has been loaded (if applicable).
 *
 * @param kmac KMAC block context.
 * @param mode Mode (security strength) for KMAC.
 * @param key KMAC key.
 * @param custom_string Customization string.
 * @param custom_string_len Length of customization string.
 * @param message Input message.
 * @param message_len Length of message in bytes.
 * @param output_len Requested length of output in words.
 * @param[out] output Pre-allocated output buffer (length must match
 * output_len).
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
status_t kmac_testutils_kmac(const dif_kmac_t *kmac, dif_kmac_mode_kmac_t mode,
                             const dif_kmac_key_t *key,
                             const char *custom_string,
                             const size_t custom_string_len,
                             const char *message, const size_t message_len,
                             const size_t output_len, uint32_t *output);

#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_KMAC_TESTUTILS_H_
