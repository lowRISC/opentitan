// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_RV_CORE_IBEX_TESTUTILS_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_RV_CORE_IBEX_TESTUTILS_H_

#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/dif/dif_rv_core_ibex.h"

/**
 * Returns the validity of random data read from the entropy source as bool.
 *
 * Returns true if the random data read from the entropy source is valid, else
 * false. Whether the random data is FIPS compliant or not is not indicated.
 * @param rv_core_ibex An rv_core_ibex handle.
 * @return The validity of random data read from the entropy source.
 */
bool rv_core_ibex_testutils_is_rnd_data_valid(
    const dif_rv_core_ibex_t *rv_core_ibex);

/**
 * Returns a random data read from the entropy source.
 *
 * A spinwait loop is invoked to wait for the random data fetched from the
 * entropy source to be valid. The spinwait times out after the timeout_usec
 * microseconds. Once valid, the random data is read and checked before it is
 * returned.
 * @param rv_core_ibex An rv_core_ibex handle.
 * @param timeout_usec Timeout in microseconds.
 * @param[out] rnd The random data read from the entropy source.
 * @return The result of the operation
 */
OT_WARN_UNUSED_RESULT
status_t rv_core_ibex_testutils_get_rnd_data(
    const dif_rv_core_ibex_t *rv_core_ibex, uint32_t timeout_usec,
    uint32_t *rnd);

#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_RV_CORE_IBEX_TESTUTILS_H_
