// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_EPMP_TEST_UNLOCK_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_EPMP_TEST_UNLOCK_H_

#include <stdbool.h>

#include "sw/device/silicon_creator/lib/epmp_state.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * Unlock the test status address space for read/write access.
 *
 * The production ePMP schema used by the ROM blocks all accesses to the
 * 4 byte test status address space. This address space is used by tests to
 * report test progress and results and so must be made accessible before tests
 * can be run.
 *
 * Utilizes a dedicated PMP entry reserved for this usage.
 *
 * @returns The result of the operation (`true` if address space unlocked
 * successfully).
 */
bool epmp_unlock_test_status(void);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_EPMP_TEST_UNLOCK_H_
