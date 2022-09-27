// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_BASE_CHIP_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_BASE_CHIP_H_

/**
 * @file
 * @brief Chip-level constants.
 */

/**
 * Manifest size for boot stages stored in flash (in bytes).
 */
#define CHIP_MANIFEST_SIZE 896

/**
 * ROM_EXT manifest identifier (ASCII "OTRE").
 */
#define CHIP_ROM_EXT_IDENTIFIER 0x4552544f

/**
 * Allowed bounds for the `length` field of a ROM_EXT manifest.
 */
#define CHIP_ROM_EXT_SIZE_MIN CHIP_MANIFEST_SIZE
#define CHIP_ROM_EXT_SIZE_MAX 0x10000

/**
 * First owner boot stage, e.g. BL0, manifest identifier (ASCII "OTB0").
 */
#define CHIP_BL0_IDENTIFIER 0x3042544f

/**
 * Allowed bounds for the `length` field of a first owner boot stage manifest.
 */
#define CHIP_BL0_SIZE_MIN CHIP_MANIFEST_SIZE
#define CHIP_BL0_SIZE_MAX 0x70000

/**
 * Value written to the end of the retention SRAM creator area by `test_rom` to
 * be able to determine the type of ROM in tests (ASCII "TEST").
 */
#define TEST_ROM_IDENTIFIER 0x54534554

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_BASE_CHIP_H_
