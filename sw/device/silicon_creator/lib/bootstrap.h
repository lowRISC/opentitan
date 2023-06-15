// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_BOOTSTRAP_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_BOOTSTRAP_H_

#include "sw/device/lib/base/hardened.h"
#include "sw/device/silicon_creator/lib/drivers/spi_device.h"
#include "sw/device/silicon_creator/lib/error.h"

#ifdef __cplusplus
extern "C" {
#endif

/**
 * @public
 * Enters flash programming mode. This function initializes the SPI device and
 * uses incoming SPI commands to drive an internal state machine.
 *
 * Dependent code should use this function as the main entry point to bootstrap.
 * The dependent code must provide implementations for the following functions:
 *   - `bootstrap_chip_erase()`
 *   - `bootstrap_erase_verify()`
 *
 * Bootstrapping uses the typical SPI flash EEPROM commands. A typical session
 * involves:
 * - Asserting bootstrap pins to enter bootstrap mode,
 * - Erasing the chip (WREN, CHIP_ERASE, busy loop ...),
 * - Programming the chip (WREN, PAGE_PROGRAM, busy loop ...), and
 * - Resetting the chip (RESET).
 *
 * This function only returns on error; a successful session ends with a chip
 * reset.
 *
 * @return The result of the flash loop.
 */
OT_WARN_UNUSED_RESULT
rom_error_t enter_bootstrap(void);

/**
 * @private @pure
 * Handles access permissions and erases both data banks of the embedded flash.
 *
 * NOTE: This abstract function must be implemented by dependent code.
 *
 * @return Result of the operation.
 */
OT_WARN_UNUSED_RESULT
rom_error_t bootstrap_chip_erase(void);

/**
 * @private @pure
 * Verify that all data banks have been erased.
 *
 * This function also clears the WIP and WEN bits of the flash status register.
 *
 * NOTE: This abstract function must be implemented by dependent code.
 *
 * @return Result of the operation.
 */
OT_WARN_UNUSED_RESULT
rom_error_t bootstrap_erase_verify(void);

#ifdef __cplusplus
}
#endif

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_BOOTSTRAP_H_
