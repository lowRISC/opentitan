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
 * First owner boot stage manifest identifier (ASCII "OTSO").
 */
#define CHIP_BL0_IDENTIFIER 0x4f53544f

/**
 * Allowed bounds for the `length` field of a first owner boot stage manifest.
 */
#define CHIP_BL0_SIZE_MIN CHIP_MANIFEST_SIZE
#define CHIP_BL0_SIZE_MAX 0x70000

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_BASE_CHIP_H_
