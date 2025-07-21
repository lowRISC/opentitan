// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_CLKMGR_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_CLKMGR_H_

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/macros.h"

#ifdef __cplusplus
extern "C" {
#endif

/**
 * Checks if the JITTER_ENABLE register of the CLKMGR is set to on.
 *
 * @return Whether the jittery clock is enabled.
 */
OT_WARN_UNUSED_RESULT
hardened_bool_t clkmgr_check_jittery_clk_en(void);

#ifdef __cplusplus
}
#endif

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_CLKMGR_H_
