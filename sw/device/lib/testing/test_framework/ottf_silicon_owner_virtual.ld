/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Linker script for OpenTitan OTTF-launched test binaries.
 *
 * Portions of this file are Ibex-specific.
 *
 * This linker script generates a binary to run BL0 tests.
 */

INCLUDE hw/top_earlgrey/sw/autogen/top_earlgrey_memory.ld

/**
 * Symbols to be used in the setup of the address translation for ROM_EXT.
 */
_ottf_size = LENGTH(owner_virtual) - _rom_ext_size;
_ottf_start_address = ORIGIN(owner_virtual) + _rom_ext_size;
ASSERT((_ottf_size <= (LENGTH(eflash) / 2)),
  "Error: BL0 flash is bigger than slot.");

REGION_ALIAS("ottf_flash", owner_virtual);

INCLUDE sw/device/lib/testing/test_framework/ottf_common.ld
