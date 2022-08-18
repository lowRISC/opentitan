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
#define MANIFEST_SIZE 896

/**
 * ROM_EXT manifest identifier (ASCII "OTRE").
 */
#define MANIFEST_IDENTIFIER_ROM_EXT 0x4552544f

/**
 * Allowed bounds for the `length` field of a ROM_EXT manifest.
 */
#define MANIFEST_LENGTH_FIELD_ROM_EXT_MIN MANIFEST_SIZE
#define MANIFEST_LENGTH_FIELD_ROM_EXT_MAX 0x10000

/**
 * First owner boot stage manifest identifier (ASCII "OTSO").
 */
#define MANIFEST_IDENTIFIER_OWNER_STAGE 0x4f53544f

/**
 * Allowed bounds for the `length` field of a first owner boot stage manifest.
 */
#define MANIFEST_LENGTH_FIELD_OWNER_STAGE_MIN MANIFEST_SIZE
#define MANIFEST_LENGTH_FIELD_OWNER_STAGE_MAX 0x70000

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_BASE_CHIP_H_
