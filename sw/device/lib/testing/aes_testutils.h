// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_AES_TESTUTILS_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_AES_TESTUTILS_H_

#include "sw/device/lib/dif/dif_aes.h"
#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/testing/check.h"

/**
 * Returns the value of the AES status flag.
 *
 * @param aes An aes DIF handle.
 * @param flag Status flag to query.
 */
inline bool aes_testutils_get_status(dif_aes_t *aes, dif_aes_status_t flag) {
  bool status;
  CHECK_DIF_OK(dif_aes_get_status(aes, flag, &status));
  return status;
}

/**
 * Waits for the given AES status flag to be set the the given value.
 *
 * @param aes An aes DIF handle.
 * @param flag Status flag to query.
 * @param value The status flag value.
 * @param timeout_usec Timeout in microseconds.
 */
inline void aes_testutils_wait_for_status(dif_aes_t *aes, dif_aes_status_t flag,
                                          bool value, uint32_t timeout_usec) {
  IBEX_SPIN_FOR(aes_testutils_get_status(aes, flag) == value, timeout_usec);
}

#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_AES_TESTUTILS_H_
