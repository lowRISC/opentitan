// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_BOOTSTRAP_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_BOOTSTRAP_H_

#ifdef __cplusplus
extern "C" {
#endif

#include "sw/device/lib/base/hardened.h"
#include "sw/device/silicon_creator/lib/error.h"

/**
 * Enters flash programming mode. This function initializes the SPI device and
 * uses incoming SPI commands to drive an internal state machine.
 *
 * Bootstrapping uses the typical SPI flash EEPROM commands. A typical session
 * involves:
 * - Asserting bootstrap pins to enter bootstrap mode,
 * - Erasing the chip (WREN, CHIP_ERASE, busy loop ...),
 * - Programming the chip (WREN, PAGE_PROGRAM, busy loop ...), and
 * - Resetting the chip (RESET).
 *
 * This function only returns on error since a successful session ends with a
 * chip reset.
 *
 * @param protect_rom_ext Whether to prevent changes to to ROM_EXT.
 * @return The result of the flash loop.
 */
rom_error_t enter_bootstrap(hardened_bool_t protect_rom_ext);

#ifdef __cplusplus
}
#endif

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_BOOTSTRAP_H_
