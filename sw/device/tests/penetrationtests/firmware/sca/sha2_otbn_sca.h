// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_FIRMWARE_SCA_SHA2_OTBN_SCA_H_
#define OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_FIRMWARE_SCA_SHA2_OTBN_SCA_H_

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/ujson/ujson.h"

/**
 * Runs a single masked/unmasked OTBN SHA-2 (SHA-256/384/512) operation.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_otbn_sca_sha2_single(ujson_t *uj);

/**
 * Runs masked/unmasked OTBN SHA-2 (SHA-256/384/512) in Fixed-vs-Random batch
 * mode.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_otbn_sca_sha2_batch_fvsr(ujson_t *uj);

/**
 * Runs masked/unmasked OTBN SHA-2 (SHA-256/384/512) in Random batch mode.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_otbn_sca_sha2_batch_random(ujson_t *uj);

#endif  // OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_FIRMWARE_SCA_SHA2_OTBN_SCA_H_
