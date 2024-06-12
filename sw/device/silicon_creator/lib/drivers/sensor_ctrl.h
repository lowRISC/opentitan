// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_SENSOR_CTRL_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_SENSOR_CTRL_H_
#include <stdint.h>

#include "sw/device/silicon_creator/lib/drivers/lifecycle.h"
#include "sw/device/silicon_creator/lib/error.h"

#ifdef __cplusplus
extern "C" {
#endif

/**
 * The following constants represent the expected number of sec_mmio register
 * writes performed by functions in provided in this module. See
 * `SEC_MMIO_WRITE_INCREMENT()` for more details.
 */
enum {
  kSensorCtrlSecMmioConfigure = 12,
};

/**
 * Number of cycles to wait for sensor_ctrl to synchronize.
 * See opentitan#23150.  Since each CDC synchronize event takes
 * 4 AON clocks, we need 5 cycles.
 */
enum {
  kSensorCtrlSyncCycles = 5,
};

/**
 * Configure sensors according to their OTP-defined configurations
 *
 * @param lc_state Life cycle state of the device.
 * @return result of the operation.
 */
OT_WARN_UNUSED_RESULT
rom_error_t sensor_ctrl_configure(lifecycle_state_t lc_state);

#ifdef __cplusplus
}
#endif
#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_SENSOR_CTRL_H_
