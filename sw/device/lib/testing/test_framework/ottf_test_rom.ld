/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Linker script for OpenTitan OTTF-launched test binaries.
 *
 * Portions of this file are Ibex-specific.
 *
 * This linker script generates a binary to run with the test rom.
 */

INCLUDE hw/top_earlgrey/sw/autogen/top_earlgrey_memory.ld

/**
 * Symbols to be used in the setup of the address translation for ROM_EXT.
 */
_ottf_ext_start_address = ORIGIN(eflash);
_ottf_ext_size = LENGTH(eflash);

REGION_ALIAS("ottf_flash", eflash);

INCLUDE sw/device/lib/testing/test_framework/ottf_common.ld
