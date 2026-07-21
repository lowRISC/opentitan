// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_MANUF_LIB_PERSONALIZE_SECRET1_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_MANUF_LIB_PERSONALIZE_SECRET1_H_

#include "sw/device/lib/base/status.h"

#ifdef __cplusplus
extern "C" {
#endif

/**
 * Provision Secret1 OTP partition.
 *
 * @return The status of the operation.
 */
OT_WARN_UNUSED_RESULT
status_t manuf_personalize_device_secret1(void);

/**
 * Check if Secret1 OTP partition is provisioned.
 *
 * @return OK if locked, error otherwise.
 */
OT_WARN_UNUSED_RESULT
status_t manuf_personalize_device_secret1_check(void);

#ifdef __cplusplus
}
#endif

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_MANUF_LIB_PERSONALIZE_SECRET1_H_
