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
#define CHIP_MANIFEST_SIZE 964

/**
 * Number of entries in the manifest extensions table.
 */
#define CHIP_MANIFEST_EXT_TABLE_ENTRY_COUNT 8

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

/**
 * Pinmux pull up/down wait delay.
 *
 * After enabling the pull-up/down on a pin, we need to wait for ~5us for the
 * configuration to propagate to the physical pads. 5us is 500 clock cycles
 * assuming a 100MHz clock.
 */
#define PINMUX_PAD_ATTR_PROP_CYCLES 500

/**
 * Pinmux peripheral input values for software strap pins.
 */
#define SW_STRAP_0_PERIPH 22
#define SW_STRAP_1_PERIPH 23
#define SW_STRAP_2_PERIPH 24

/**
 * Pinmux MIO input selector values for software strap pins.
 */
#define SW_STRAP_0_INSEL 24
#define SW_STRAP_1_INSEL 25
#define SW_STRAP_2_INSEL 26

/**
 * Pads of the software strap pins.
 */
#define SW_STRAP_0_PAD 22
#define SW_STRAP_1_PAD 23
#define SW_STRAP_2_PAD 24

/**
 * Mask for the software strap pins.
 */
#define SW_STRAP_MASK                                    \
  ((1 << SW_STRAP_2_PERIPH) | (1 << SW_STRAP_1_PERIPH) | \
   (1 << SW_STRAP_0_PERIPH))

/**
 * RMA entry strap value.
 *
 * We expect strong pull-ups on SW_STRAP_2_PERIPH and SW_STRAP_1_PERIPH, and
 * strong pull-down on SW_STRAP_0_PERIPH, i.e. `11_11_00`.
 */
#define SW_STRAP_RMA_ENTRY                               \
  ((1 << SW_STRAP_2_PERIPH) | (1 << SW_STRAP_1_PERIPH) | \
   (0 << SW_STRAP_0_PERIPH))

/**
 * Bootstrap strap value.
 *
 * We expect strong pull-ups on all software strap pins, i.e. `11_11_11`.
 */
#define SW_STRAP_BOOTSTRAP                               \
  ((1 << SW_STRAP_2_PERIPH) | (1 << SW_STRAP_1_PERIPH) | \
   (1 << SW_STRAP_0_PERIPH))

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_BASE_CHIP_H_
