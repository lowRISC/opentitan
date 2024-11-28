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

INCLUDE @@TOP_MEMORY_LD@@
INCLUDE @@OTTF_LD_ALIAS@@

/**
 * Symbols to be used in the setup of the address translation for the OTTF run
 * at the BL0 boot stage in slot B.
 */
/* TODO(#9045): Move ROM_EXT size to a common location. */
_ottf_size = (LENGTH(ottf_flash) / 2) - 0x10000;
_ottf_start_address = ORIGIN(ottf_flash) + (LENGTH(ottf_flash) / 2) + 0x10000;

INCLUDE @@OTTF_LD_COMMON@@
