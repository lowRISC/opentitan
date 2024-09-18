// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_FIRMWARE_SCA_KMAC_SCA_H_
#define OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_FIRMWARE_SCA_KMAC_SCA_H_

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/ujson/ujson.h"

/**
 * The result of an KMAC SCA operation.
 */
typedef enum kmac_sca_error {
  /**
   * Indicates that the operation succeeded.
   */
  kmacScaOk = 0,
  /**
   * Indicates some unspecified failure.
   */
  kmacScaAborted = 1,
  /**
   * Indicates that the attempted operation would attempt a read/write to an
   * address that would go out of range.
   */
  kmacScaOutOfRange = 2
} kmac_sca_error_t;

status_t handle_kmac_pentest_seed_lfsr(ujson_t *uj);
status_t handle_kmac_sca_fixed_key_set(ujson_t *uj);
status_t handle_kmac_sca_batch(ujson_t *uj);
status_t handle_kmac_sca_single_absorb(ujson_t *uj);
status_t handle_kmac_sca_set_key(ujson_t *uj);
status_t handle_kmac_pentest_init(ujson_t *uj);
status_t handle_kmac_sca(ujson_t *uj);

#endif  // OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_FIRMWARE_SCA_KMAC_SCA_H_
