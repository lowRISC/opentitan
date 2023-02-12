/* Copyright lowRISC contributors. */
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
 * Symbols to be used in the setup of the address translation for the OTTF run
 * at the BL0 boot stage in slot A.
 */
/* TODO(#9045): Move ROM_EXT size to a common location. */
_ottf_size = (LENGTH(eflash) / 2) - 0x10000;
_ottf_start_address = ORIGIN(eflash) + 0x10000;

REGION_ALIAS("ottf_flash", eflash);

INCLUDE sw/device/lib/testing/test_framework/ottf_common.ld
