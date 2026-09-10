// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_TESTS_CRYPTO_CRYPTOTEST_FIRMWARE_MLDSA_H_
#define OPENTITAN_SW_DEVICE_TESTS_CRYPTO_CRYPTOTEST_FIRMWARE_MLDSA_H_

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/ujson/ujson.h"

#ifdef __cplusplus
extern "C" {
#endif

/**
 * Command handler for ML-DSA commands.
 *
 * @param uj uJSON context.
 * @return Result of the operation.
 */
status_t handle_mldsa(ujson_t *uj);

#ifdef __cplusplus
}
#endif

#endif  // OPENTITAN_SW_DEVICE_TESTS_CRYPTO_CRYPTOTEST_FIRMWARE_MLDSA_H_
