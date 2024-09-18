// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_FIRMWARE_SCA_HMAC_SCA_H_
#define OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_FIRMWARE_SCA_HMAC_SCA_H_

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/ujson/ujson.h"

/**
 * Initializes the trigger and configures the device for the HMAC SCA test.
 *
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_hmac_pentest_init(ujson_t *uj);

/**
 * hmac.sca.batch_fvsr test
 *
 * This SCA penetration test triggers num_iterations HMAC-SHA256 operations
 * using a Fixed vs Random (FvsR) dataset. This dataset is generated on the
 * device using the PRNG from the SCA library.
 *
 * SCA traces are captured during trigger_high & trigger_low.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_hmac_sca_batch_fvsr(ujson_t *uj);

/**
 * hmac.sca.batch_random test
 *
 * This SCA penetration test triggers num_iterations HMAC-SHA256 operations
 * using a random dataset. This dataset is generated on the device using the
 * PRNG from the SCA library.
 *
 * SCA traces are captured during trigger_high & trigger_low.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_hmac_sca_batch_random(ujson_t *uj);

/**
 * hmac.sca.single test
 *
 * This SCA penetration test triggers a single HMAC-SHA256 operation using the
 * provided key, mask, and message. The tag is returend to the host.
 *
 * SCA traces are captured during trigger_high & trigger_low.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_hmac_sca_single(ujson_t *uj);

/**
 * HMAC SCA command handler.
 *
 * Command handler for the HMAC SCA command.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_hmac_sca(ujson_t *uj);

#endif  // OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_FIRMWARE_SCA_HMAC_SCA_H_
