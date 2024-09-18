// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_FIRMWARE_SCA_SHA3_SCA_H_
#define OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_FIRMWARE_SCA_SHA3_SCA_H_

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/ujson/ujson.h"

/**
 * The result of an SHA SCA operation.
 */
typedef enum sha3_sca_error {
  /**
   * Indicates that the operation succeeded.
   */
  sha3ScaOk = 0,
  /**
   * Indicates some unspecified failure.
   */
  sha3ScaAborted = 1,
  /**
   * Indicates that the attempted operation would attempt a read/write to an
   * address that would go out of range.
   */
  sha3ScaOutOfRange = 2
} sha3_sca_error_t;

status_t handle_sha3_sca_disable_masking(ujson_t *uj);
status_t handle_sha3_pentest_seed_lfsr(ujson_t *uj);
status_t handle_sha3_sca_fixed_message_set(ujson_t *uj);
status_t handle_sha3_sca_batch(ujson_t *uj);
status_t handle_sha3_sca_single_absorb(ujson_t *uj);
status_t handle_sha3_pentest_init(ujson_t *uj);
status_t handle_sha3_sca(ujson_t *uj);

#endif  // OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_FIRMWARE_SCA_SHA3_SCA_H_
