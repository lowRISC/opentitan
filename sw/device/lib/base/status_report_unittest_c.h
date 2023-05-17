// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_BASE_STATUS_REPORT_UNITTEST_C_H_
#define OPENTITAN_SW_DEVICE_LIB_BASE_STATUS_REPORT_UNITTEST_C_H_

#include "sw/device/lib/base/status.h"

#ifdef __cplusplus
extern "C" {
#endif

/**
 * A test that uses TRY() to exercises status_report()
 */
status_t status_report_unittest_c();

#ifdef __cplusplus
}
#endif
#endif  // OPENTITAN_SW_DEVICE_LIB_BASE_STATUS_REPORT_UNITTEST_C_H_
