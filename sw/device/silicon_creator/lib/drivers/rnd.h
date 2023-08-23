// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_RND_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_RND_H_

#include "sw/device/silicon_creator/lib/drivers/lifecycle.h"
#include "sw/lib/sw/device/base/macros.h"
#include "sw/lib/sw/device/silicon_creator/error.h"

#ifdef __cplusplus
extern "C" {
#endif

/**
 * Returns a random word from the RISC-V Ibex core wrapper.
 *
 * Requires the CREATOR_SW_CFG_RNG_EN OTP value set to `kHardenedBoolTrue`
 * in order to enable the use of entropy, otherwise it only returns the current
 * value of the MCYCLE CSR register.
 *
 * @returns MCYCLE CSR + entropy value.
 */
OT_WARN_UNUSED_RESULT
uint32_t rnd_uint32(void);

#ifdef __cplusplus
}
#endif

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_RND_H_
