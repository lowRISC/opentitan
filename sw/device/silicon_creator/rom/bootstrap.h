// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_ROM_BOOTSTRAP_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_ROM_BOOTSTRAP_H_

#include "sw/device/lib/base/hardened.h"
#include "sw/device/silicon_creator/lib/error.h"

#ifdef __cplusplus
extern "C" {
#endif

/**
 * Checks whether bootstrap is requested.
 *
 * The return value of this function also depends on the `ROM_BOOTSTRAP_DIS` OTP
 * item.
 *
 * @return Whether bootstrap is requested.
 */
OT_WARN_UNUSED_RESULT
hardened_bool_t bootstrap_requested(void);

/**
 * Bootstraps the data partition of the embedded flash with data received by the
 * spi_device.
 *
 * OpenTitan bootstrap uses the typical SPI flash EEPROM commands. A typical
 * bootstrap session involves:
 * - Erasing the chip (WREN, CHIP_ERASE, busy loop ...),
 * - Programming the chip (WREN, PAGE_PROGRAM, busy loop ...), and
 * - Resetting the chip (RESET).
 *
 * This function only returns on error since a successful bootstrap ends with a
 * chip reset.
 *
 * @return Result of the operation.
 */
OT_WARN_UNUSED_RESULT
rom_error_t bootstrap(void);

#ifdef __cplusplus
}
#endif

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_ROM_BOOTSTRAP_H_
