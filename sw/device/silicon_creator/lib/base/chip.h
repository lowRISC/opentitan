// Copyright lowRISC contributors (OpenTitan project).
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
#define CHIP_MANIFEST_SIZE 1024

/**
 * Manifest format major and minor versions.
 */
#define CHIP_MANIFEST_VERSION_MINOR_1 0x6c47
#define CHIP_MANIFEST_VERSION_MAJOR_1 0x71c3

// TODO(moidx): Update to a valid number once we figure out a manifest
// versioning scheme.
#define CHIP_MANIFEST_VERSION_MAJOR_2 0x0002

/**
 * Number of entries in the manifest extensions table.
 */
#define CHIP_MANIFEST_EXT_TABLE_ENTRY_COUNT 15

/**
 * Size of the header of a boot services message.
 */
#define CHIP_BOOT_SVC_MSG_HEADER_SIZE 44

/**
 * Maximum size of a boot services message.
 */
#define CHIP_BOOT_SVC_MSG_SIZE_MAX 256

/**
 * Maximum payload size for a boot services message.
 */
#define CHIP_BOOT_SVC_MSG_PAYLOAD_SIZE_MAX \
  (CHIP_BOOT_SVC_MSG_SIZE_MAX - CHIP_BOOT_SVC_MSG_HEADER_SIZE)

/**
 * First owner boot stage, e.g. BL0, manifest identifier (ASCII "OTB0").
 */
#define CHIP_BL0_IDENTIFIER 0x3042544f

/**
 * Allowed bounds for the `length` field of a first owner boot stage manifest.
 */
#define CHIP_BL0_SIZE_MIN CHIP_MANIFEST_SIZE
#ifndef OT_COVERAGE_ENABLED
#define CHIP_BL0_SIZE_MAX 0x70000
#else  // OT_COVERAGE_ENABLED
#define CHIP_BL0_SIZE_MAX 0x60000
#endif  // OT_COVERAGE_ENABLED

/**
 * ROM_EXT manifest identifier (ASCII "OTRE").
 */
#define CHIP_ROM_EXT_IDENTIFIER 0x4552544f

/**
 * Allowed bounds for the `length` field of a ROM_EXT manifest.
 */
#define CHIP_ROM_EXT_SIZE_MIN CHIP_MANIFEST_SIZE
#ifndef OT_COVERAGE_ENABLED
#define CHIP_ROM_EXT_SIZE_MAX 0x10000
#else  // OT_COVERAGE_ENABLED
#define CHIP_ROM_EXT_SIZE_MAX 0x20000
#endif  // OT_COVERAGE_ENABLED
#define CHIP_ROM_EXT_RESIZABLE_SIZE_MAX \
  (CHIP_ROM_EXT_SIZE_MAX + CHIP_BL0_SIZE_MAX)

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
 * Pinmux peripheral input values for software strap pins: gpio1 pins 2-4, see
 * SW_STRAP_n_GPIO.
 */
#define SW_STRAP_0_PERIPH 46
#define SW_STRAP_1_PERIPH 47
#define SW_STRAP_2_PERIPH 48

/**
 * Pinmux MIO input selector values for software strap pins.
 */
#define SW_STRAP_0_INSEL 36
#define SW_STRAP_1_INSEL 37
#define SW_STRAP_2_INSEL 38

/**
 * Pads of the software strap pins.
 */
#define SW_STRAP_0_PAD 34
#define SW_STRAP_1_PAD 35
#define SW_STRAP_2_PAD 36

/**
 * Bits of the software strap pins in the DATA_IN register of their GPIO
 * instance (gpio1 for EG).
 */
#define SW_STRAP_0_GPIO 2
#define SW_STRAP_1_GPIO 3
#define SW_STRAP_2_GPIO 4

/**
 * Mask for the software strap pins.
 */
#define SW_STRAP_MASK \
  ((1 << SW_STRAP_2_GPIO) | (1 << SW_STRAP_1_GPIO) | (1 << SW_STRAP_0_GPIO))

/**
 * RMA entry strap value.
 *
 * We expect strong pull-ups on SW_STRAP_2 and SW_STRAP_1, and strong
 * pull-down on SW_STRAP_0, i.e. `11_11_00`.
 */
#define SW_STRAP_RMA_ENTRY \
  ((1 << SW_STRAP_2_GPIO) | (1 << SW_STRAP_1_GPIO) | (0 << SW_STRAP_0_GPIO))

/**
 * Bootstrap strap value.
 *
 * We expect strong pull-ups on all software strap pins, i.e. `11_11_11`.
 */
#define SW_STRAP_BOOTSTRAP \
  ((1 << SW_STRAP_2_GPIO) | (1 << SW_STRAP_1_GPIO) | (1 << SW_STRAP_0_GPIO))

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_BASE_CHIP_H_
