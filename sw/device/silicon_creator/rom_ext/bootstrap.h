// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_ROM_EXT_BOOTSTRAP_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_ROM_EXT_BOOTSTRAP_H_

#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/silicon_creator/lib/error.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * Checks whether recovery is enabled.
 *
 * Returns `kHardenedBoolTrue` iff recovery is enabled in OTP and the reset
 * reason is power on reset. Otherwise, it returns `kHardenedBoolFalse`.
 *
 * @return Whether recovery may proceed.
 */
OT_WARN_UNUSED_RESULT
hardened_bool_t rom_ext_bootstrap_enabled(void);

/**
 * Bootstraps the data partition of the embedded flash with data received by the
 * spi_device. This function will never erase or reprogram ROM_EXT's flash
 * regions in slot A or slot B.
 *
 * OpenTitan bootstrap uses the typical SPI flash EEPROM commands. A typical
 * bootstrap session involves:
 * - Asserting bootstrap pins to enter bootstrap mode,
 * - Erasing the chip (WREN, CHIP_ERASE, busy loop ...),
 * - Programming the chip (WREN, PAGE_PROGRAM, busy loop ...), and
 * - Resetting the chip (RESET).
 *
 * TODO(#19151) Configure flash memory protection hardware. Until we do this,
 * the flash restrictions described below are not enforced.
 *
 * This function configures flash memory protection to control which operations
 * can be performed on individual regions, e.g. the ROM_EXT in slot A should be
 * non-erasable and non-programmable. In more detail:
 *
 *   | Flash Region     | Erasable | Programmable |
 *   |------------------|----------|--------------|
 *   | Slot A ROM_EXT   | No       | No           |
 *   | Slot A remainder | Yes      | Yes          |
 *   | Slot B ROM_EXT   | No       | No           |
 *   | Slot B remainder | Yes      | No           |
 *
 * This function only returns on error since a successful bootstrap ends with a
 * chip reset.
 *
 * @return The error that caused recovery to fail.
 */
OT_WARN_UNUSED_RESULT
rom_error_t rom_ext_bootstrap(void);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_ROM_EXT_BOOTSTRAP_H_
