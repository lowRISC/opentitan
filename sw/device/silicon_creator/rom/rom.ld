/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Linker script for an OpenTitan ROM.
 *
 * Portions of this file are Ibex-specific.
 */


INCLUDE hw/top_earlgrey/sw/autogen/top_earlgrey_memory.ld

/**
 * The boot address, which indicates the location of the initial interrupt
 * vector.
 */
_rom_boot_address = ORIGIN(rom);

REGION_ALIAS("rom_region", rom);

INCLUDE sw/device/silicon_creator/rom/rom_common.ld
