/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Linker script for OpenTitan OTTF-launched test binaries.
 *
 * Portions of this file are Ibex-specific.
 *
 * This linker script generates a binary to run rom.
 */

INCLUDE @@TOP_MEMORY_LD@@

/**
 * Symbols to be used in the setup of the address translation for the OTTF run
 * at the Silicon Creator boot stage in the virtual slot.
 */
_ottf_start_address = ORIGIN(@@OTTF_REGION_ALIAS@@);
_ottf_size = LENGTH(@@OTTF_REGION_ALIAS@@);

REGION_ALIAS("ottf_flash", rom_ext_virtual);

INCLUDE @@OTTF_LD_COMMON@@
